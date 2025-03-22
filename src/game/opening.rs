//! # Opening format
//! Horsey stores opening information (name, moves, WDL score, etc) as a tree.
//!
//! Nodes of the tree contain:
//! - name of the opening (if any)
//! - WDL score for the side to move
//! - move to play
//!
//! The children of a node represent accessible opening continuations. By going down
//! the tree, one can select opening moves, access information about them, etc.

use std::{
    borrow::Cow,
    rc::{Rc, Weak},
};

use super::{
    action::{Action, LegalAction},
    score::WinProbability,
};

/// An opening node, with information on win probability, name of the opening and
/// last action taken, as well as actions that can be taken from this opening.
struct OpeningNode<'a> {
    win_probability: f32,
    name: Cow<'a, str>,
    action: LegalAction,
    parent: Option<Weak<OpeningNode<'a>>>,
    children: Vec<Rc<OpeningNode<'a>>>,
}

pub struct Opening<'a> {
    root: Rc<OpeningNode<'a>>,
}
impl<'a> Opening<'a> {
    /// Returns the sequence of actions to play in this opening.
    pub fn actions(&self) -> Vec<Action> {
        let mut actions = vec![];
        let mut current_node = self.root.clone();
        while let Some(parent) = current_node.parent.as_ref() {
            actions.push(current_node.action.downgrade());
            current_node = parent.upgrade().unwrap()
        }
        actions
    }

    /// Returns the name of this opening.
    pub fn name(&self) -> &str {
        &self.root.name
    }

    /// Returns the win probability for this opening, from the side to move's
    /// perspective.
    pub fn win_probability(&self) -> WinProbability {
        self.root.win_probability
    }

    /// Moves to a child of the current node associated with the given action.
    /// # Errors
    /// If no child of this node is marked with the given action, returns an error.
    pub fn play(&mut self, action: Action) -> Result<(), ()> {
        if let Some(child) = self
            .root
            .children
            .iter()
            .find(|node| node.action.downgrade() == action)
        {
            self.root = child.clone();
            Ok(())
        } else {
            Err(())
        }
    }
}
