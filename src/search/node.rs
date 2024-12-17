use std::{
    cell::UnsafeCell,
    sync::{
        atomic::{AtomicBool, AtomicI16, AtomicU64, Ordering},
        Arc, Weak,
    },
};

use crate::game::{action::Action, colour::Colour, position::Position};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    WinProbability {
        wins: i32,
        samples: u32,
        perspective: Colour,
    },
    Win(Colour),
    Draw,
}
impl Value {
    pub fn exploitation_score(self, perspective: Colour) -> f32 {
        match self {
            Self::WinProbability {
                wins,
                samples,
                perspective: p,
            } => {
                let win_probability = wins as f32 / samples as f32;
                if perspective == p {
                    win_probability
                } else {
                    -win_probability
                }
            }
            Self::Draw => 0.,
            Self::Win(colour) => {
                if colour == perspective {
                    1.
                } else {
                    -1.
                }
            }
        }
    }
}

/// MCTS node that is accessible through threads lock-free.
pub struct Node {
    perspective: Colour,
    action: Option<Action>,
    score_visits: AtomicU64,
    children: UnsafeCell<Vec<Arc<Node>>>,
    parent: Option<Weak<Node>>,

    // Metadata
    is_parent: AtomicBool,
    non_expanded_children: AtomicI16,
    expandable: AtomicBool,
    fully_expanded: AtomicBool,
}
impl Node {
    /// Creates a new root node.
    pub fn new_root(perspective: Colour) -> Arc<Self> {
        Arc::new(Self {
            perspective,
            action: None,
            score_visits: AtomicU64::new(0),
            children: UnsafeCell::new(vec![]),
            parent: None,

            is_parent: AtomicBool::new(false),
            non_expanded_children: AtomicI16::new(-1),
            expandable: AtomicBool::new(false),
            fully_expanded: AtomicBool::new(false),
        })
    }

    /// Creates a new node with the given parent and leading action.
    pub fn new(perspective: Colour, action: Action, parent: Weak<Self>) -> Arc<Self> {
        Arc::new(Self {
            perspective,
            action: Some(action),
            score_visits: AtomicU64::new(0),
            children: UnsafeCell::new(vec![]),
            parent: Some(parent),

            is_parent: AtomicBool::new(false),
            non_expanded_children: AtomicI16::new(-1),
            expandable: AtomicBool::new(false),
            fully_expanded: AtomicBool::new(false),
        })
    }

    /// Returns the action that led to this node.
    pub fn action(&self) -> Option<Action> {
        self.action
    }

    /// Returns this node's parent.
    pub fn parent(&self) -> Option<Arc<Self>> {
        self.parent.clone().and_then(|p| p.upgrade())
    }

    /// Initializes the children attribute of this node.
    pub fn init_children(node: Arc<Self>, position: &Position) {
        if !node.is_parent.swap(true, Ordering::SeqCst) {
            let mut actions_count = -1;
            for action in position.actions() {
                unsafe {
                    node.children.get().as_mut().unwrap().push(Self::new(
                        node.perspective.inverse(),
                        action,
                        Arc::downgrade(&node),
                    ));
                }
                actions_count += 1;
            }
            if actions_count >= 0 {
                node.non_expanded_children
                    .store(actions_count, Ordering::SeqCst);
                node.expandable.store(true, Ordering::Release)
            } else {
                node.fully_expanded.store(true, Ordering::SeqCst)
            }
        }
    }

    /// Expands a new child node.
    pub fn add_child(&self) -> Option<Arc<Self>> {
        if self.expandable.load(Ordering::Acquire) {
            let i: i16 = self.non_expanded_children.fetch_sub(1, Ordering::SeqCst);
            if i == 0 {
                self.expandable.store(true, Ordering::SeqCst);
                self.fully_expanded.store(true, Ordering::SeqCst)
            }
            if i < 0 {
                None
            } else {
                unsafe { Some(self.children.get().as_ref().unwrap()[i as usize].clone()) }
            }
        } else {
            None
        }
    }

    /// Checks if this node has all its children expanded.
    pub fn is_fully_expanded(&self) -> bool {
        self.fully_expanded.load(Ordering::SeqCst)
    }

    fn wins_and_visits(&self) -> (i32, u32) {
        let wv = self.score_visits.load(Ordering::SeqCst);
        let wins = (wv >> 32) as i32;
        let visits = (wv & 0xFFFFFFFF) as u32;
        (wins, visits)
    }

    /// Returns the value of this node.
    pub fn value(&self) -> Value {
        let (wins, visits) = self.wins_and_visits();
        if visits == u32::MAX {
            match wins.cmp(&0) {
                std::cmp::Ordering::Equal => Value::Draw,
                std::cmp::Ordering::Greater => Value::Win(self.perspective),
                _ => Value::Win(self.perspective.inverse()),
            }
        } else {
            Value::WinProbability {
                wins,
                samples: visits,
                perspective: self.perspective,
            }
        }
    }

    /// Modifies the value of this node by adding delta of value or setting it
    /// to a known value.
    pub fn update_value(&self, value: Value) {
        let (wins, samples) = match value {
            Value::WinProbability {
                wins,
                samples,
                perspective,
            } => (
                if perspective == self.perspective {
                    wins
                } else {
                    -wins
                },
                samples,
            ),
            Value::Win(colour) => {
                if colour == self.perspective {
                    (1, 1)
                } else {
                    (-1, 1)
                }
            }
            Value::Draw => (0, 1),
        };
        let sv = (wins as u64) << 32 | samples as u64;
        self.score_visits.fetch_add(sv, Ordering::SeqCst);
    }

    /// Marks the node with a virtual loss.
    pub fn add_virtual_loss(&self) {
        self.score_visits.fetch_add(1, Ordering::SeqCst);
    }

    /// Removes a virtual loss from this node.
    pub fn remove_virtual_loss(&self) {
        self.score_visits.fetch_sub(1, Ordering::SeqCst);
    }

    /// Returns the UCT score of this node.
    pub fn uct(&self, parent_visits: u32) -> f32 {
        let (wins, visits) = self.wins_and_visits();
        let exploitation = -wins as f32 / visits as f32;
        let exploration = ((2f32 * (parent_visits as f32).ln()) / visits as f32).sqrt();
        exploitation + 2f32.sqrt() * exploration
    }

    /// Returns the most promising child according to the UCT formula.
    pub fn most_promising_child(&self) -> Option<&Arc<Self>> {
        let (_, visits) = self.wins_and_visits();
        let children = unsafe { self.children.get().as_ref().unwrap() };
        children
            .iter()
            .max_by(|c1, c2| c1.uct(visits).total_cmp(&c2.uct(visits)))
    }

    /// Returns the best child of this node.
    pub fn best_child(&self) -> Option<&Arc<Self>> {
        let children = unsafe { self.children.get().as_ref().unwrap() };
        children.iter().max_by(|c1, c2| {
            c1.value()
                .exploitation_score(self.perspective)
                .total_cmp(&c2.value().exploitation_score(self.perspective))
        })
    }

    /// Returns the best move from this node.
    pub fn best_move(&self) -> Option<Action> {
        self.best_child().and_then(|c| c.action())
    }

    /// Returns the principal variation starting from this node.
    pub fn principal_variation(&self) -> Vec<Action> {
        let mut pv = vec![];
        let Some(mut node) = self.best_child() else {
            return pv;
        };

        loop {
            pv.push(node.action().unwrap());
            let Some(n) = node.best_child() else { break };
            node = n
        }

        pv
    }

    pub fn _policy(&self) -> Vec<(Action, Value)> {
        let children = unsafe { self.children.get().as_ref().unwrap() };
        children
            .iter()
            .map(|child| (child.action.unwrap(), child.value()))
            .collect()
    }
}
unsafe impl Send for Node {}
unsafe impl Sync for Node {}
