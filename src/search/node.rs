use std::{
    cell::UnsafeCell,
    sync::{
        atomic::{AtomicBool, AtomicI16, AtomicU64, Ordering},
        Arc, Weak,
    },
};

use crate::game::{action::LegalAction, colour::Colour, position::Position};

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Value {
    WinProbability {
        score: f32,
        visits: u32,
        colour: Colour,
    },
    Win(Colour),
    Draw,
}
impl Value {
    pub fn is_certain(self) -> bool {
        matches!(self, Self::Win(_) | Self::Draw)
    }

    pub fn exploitation_score(self, perspective: Colour) -> f32 {
        match self {
            Self::WinProbability {
                score,
                visits,
                colour,
            } => {
                if perspective == colour {
                    score / visits as f32
                } else {
                    -score / visits as f32
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
    action: Option<LegalAction>,
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
    pub fn new(perspective: Colour, action: LegalAction, parent: Weak<Self>) -> Arc<Self> {
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
    pub fn action(&self) -> Option<LegalAction> {
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
            for action in position.actions().0 {
                unsafe {
                    node.children.get().as_mut().unwrap().push(Self::new(
                        node.perspective.inverse(),
                        action,
                        Arc::downgrade(&node),
                    ));
                }
                actions_count += 1;
            }
            node.non_expanded_children
                .store(actions_count, Ordering::SeqCst);
            node.expandable.store(true, Ordering::Release)
        }
    }

    /// Expands a new child node.
    pub fn add_child(&self) -> Option<Arc<Self>> {
        if self.expandable.load(Ordering::Acquire) {
            let i: i16 = self.non_expanded_children.fetch_sub(1, Ordering::SeqCst);
            if i == 0 {
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

    /// Returns the value of this node.
    pub fn value(&self) -> Value {
        let sv = self.score_visits.load(Ordering::SeqCst);
        let score = f32::from_bits((sv >> 32) as u32);
        let visits = (sv & 0xFFFFFFFF) as u32;
        if score.is_nan() {
            Value::Draw
        } else if score == f32::INFINITY {
            Value::Win(self.perspective)
        } else if score == f32::NEG_INFINITY {
            Value::Win(self.perspective.inverse())
        } else {
            Value::WinProbability {
                score,
                visits,
                colour: self.perspective,
            }
        }
    }

    /// Modifies the value of this node by adding delta of value or setting it
    /// to a known value.
    pub fn update_value(&self, value: Value) {
        let (score, visits) = match value {
            Value::WinProbability {
                score,
                visits,
                colour,
            } => {
                let score = if colour == self.perspective {
                    score
                } else {
                    -score
                };
                (score, visits)
            }
            Value::Win(colour) => (if colour == self.perspective { 1. } else { -1. }, 1),
            Value::Draw => (0., 1),
        };
        let sv = (score.to_bits() as u64) << 32 | visits as u64;
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

    /// Returns the exploitation score of this node.
    pub fn exploitation_score(&self) -> f32 {
        self.value().exploitation_score(self.perspective)
    }

    /// Returns the UCT score of this node.
    pub fn uct(&self, parent_visits: u32) -> f32 {
        if let Value::WinProbability { visits, .. } = self.value() {
            let exploitation = self.exploitation_score();
            let exploration = ((2f32 * (parent_visits as f32).ln()) / visits as f32).sqrt();
            exploitation + 2f32.sqrt() * exploration
        } else {
            self.value().exploitation_score(self.perspective)
        }
    }

    /// Returns the most promising child according to the UCT formula.
    pub fn most_promising_child(&self) -> Option<&Arc<Self>> {
        let Value::WinProbability { visits, .. } = self.value() else {
            let sv = self.score_visits.load(Ordering::SeqCst);
            let score = f32::from_bits((sv >> 32) as u32);
            let visits = (sv & 0xFFFFFFFF) as u32;
            println!(
                "Score is not a win probability: {:?}, score: {}, visits: {}",
                self.value(),
                score,
                visits
            );
            return None;
        };
        let children = unsafe { self.children.get().as_ref().unwrap() };
        children
            .iter()
            .max_by(|c1, c2| c1.uct(visits).total_cmp(&c2.uct(visits)))
    }

    /// Returns the best child of this node.
    pub fn best_child(&self) -> Option<&Arc<Self>> {
        let children = unsafe { self.children.get().as_ref().unwrap() };
        children
            .iter()
            .max_by(|c1, c2| c1.exploitation_score().total_cmp(&c2.exploitation_score()))
    }

    /// Returns the best move from this node.
    pub fn best_move(&self) -> Option<LegalAction> {
        self.best_child().and_then(|c| c.action())
    }

    /// Returns the principal variation starting from this node.
    pub fn principal_variation(&self) -> Vec<LegalAction> {
        let mut pv = vec![];
        let Some(mut node) = self.best_child() else {
            return pv;
        };

        while node.is_fully_expanded() {
            pv.push(node.action().unwrap());
            let Some(n) = node.best_child() else {
                return pv;
            };
            node = n
        }

        pv
    }
}
unsafe impl Send for Node {}
unsafe impl Sync for Node {}
