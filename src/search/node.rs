use std::{
    cell::UnsafeCell,
    sync::{
        atomic::{AtomicBool, AtomicI16, AtomicU64, Ordering},
        Arc, Weak,
    },
};

use crate::game::{action::LegalAction, position::Position};

/// MCTS node that is accessible through threads lock-free.
pub struct Node {
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
    pub fn new_root() -> Arc<Self> {
        Arc::new(Self {
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
    pub fn new(action: LegalAction, parent: Weak<Self>) -> Arc<Self> {
        Arc::new(Self {
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
            let mut actions_count = 0;
            for action in position.actions().0 {
                unsafe {
                    node.children
                        .get()
                        .as_mut()
                        .unwrap()
                        .push(Self::new(action, Arc::downgrade(&node)));
                }
                actions_count += 1;
            }
            node.non_expanded_children
                .store(actions_count - 1, Ordering::SeqCst);
            node.expandable.store(true, Ordering::Release)
        }
    }

    /// Expands a new child node.
    pub fn add_child(&self) -> Option<Arc<Self>> {
        if self.expandable.load(Ordering::Acquire) {
            let i = self.non_expanded_children.fetch_sub(1, Ordering::SeqCst);
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

    /// Returns the score and visits of this node.
    pub fn score_and_visits(&self) -> (f32, u32) {
        let sv = self.score_visits.load(Ordering::SeqCst);
        let score = f32::from_bits((sv >> 32) as u32);
        let visits = (sv & 0xFFFFFFFF) as u32;
        (score, visits)
    }

    /// Modifies the score of this node by `delta`, adding one visit in the process.
    pub fn modify_score(&self, delta: f32) {
        let sv = ((delta.to_bits() as u64) << 32) | 1;
        self.score_visits.fetch_add(sv, Ordering::SeqCst);
    }

    /// Returns the exploitation score of this node.
    pub fn exploitation_score(&self) -> f32 {
        let (score, visits) = self.score_and_visits();
        score / visits as f32
    }

    /// Returns the UCT score of this node.
    pub fn uct(&self, parent_visits: u32) -> f32 {
        let (score, visits) = self.score_and_visits();
        let exploitation = score / visits as f32;
        let exploration = ((2f32 * (parent_visits as f32).ln()) / visits as f32).sqrt();
        exploitation + 2f32.sqrt() * exploration
    }

    /// Returns the most promising child according to the UCT formula.
    pub fn most_promising_child(&self) -> Arc<Self> {
        let (_, visits) = self.score_and_visits();
        let children = unsafe { self.children.get().as_ref().unwrap() };
        children
            .iter()
            .max_by(|c1, c2| c1.uct(visits).total_cmp(&c2.uct(visits)))
            .unwrap()
            .clone()
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
