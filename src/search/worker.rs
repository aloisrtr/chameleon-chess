//! # MCTS worker thread.

use std::{
    io::Write,
    sync::{
        atomic::{AtomicBool, AtomicU64, Ordering},
        Arc, Mutex,
    },
    time::{Duration, Instant},
};

use rand::{seq::SliceRandom, thread_rng};

use crate::{
    board::position::Position,
    protocols::uci::{
        commands::{UciInformation, UciMessage},
        endpoint::UciWriter,
    },
};

use super::node::Node;

pub struct MctsWorker<O: Write> {
    pub id: u32,
    pub root: Arc<Node>,
    pub max_depth: u8,
    pub depth: u8,

    // Search budget
    pub max_duration: Duration,
    pub start_time: Instant,
    pub max_nodes: u64,
    pub current_nodes: Arc<AtomicU64>,
    pub should_stop: Arc<AtomicBool>,

    // Output to UCI
    pub writer: Arc<Mutex<UciWriter<O>>>,
}
impl<O: Write> MctsWorker<O> {
    /// Runs the search on this worker's search tree.
    pub fn search(mut self, mut position: Position) {
        let mut info_tick = Instant::now();
        while self.within_budget() {
            self.depth = 0;
            let selected = self.select(self.root.clone(), &mut position);
            let expanded = self.expand(selected, &mut position);
            let reward = Self::playout(&mut position);
            Self::backup(expanded, reward, &mut position);

            if info_tick.elapsed() > Duration::from_secs(1) {
                info_tick = Instant::now();
                if self.id == 0 {
                    self.send_info().unwrap();
                }
                self.send_current_line().unwrap();
            }
        }

        if self.id == 0 {
            self.send_info().unwrap();
            self.root.best_move().map(|m| {
                self.writer
                    .lock()
                    .unwrap()
                    .send_message(UciMessage::SearchResult {
                        best: m.downgrade(),
                        ponder_on: None,
                    })
                    .unwrap()
            });
        }
    }

    pub fn within_budget(&self) -> bool {
        !self.should_stop.load(Ordering::Relaxed)
            && (self.start_time.elapsed() < self.max_duration)
            && (self.current_nodes.load(Ordering::Relaxed) <= self.max_nodes)
            && (self.depth <= self.max_depth)
    }

    /// Selects the most promising leaf node.
    fn select(&mut self, mut node: Arc<Node>, position: &mut Position) -> Arc<Node> {
        while node.is_fully_expanded()
            && !(position.threefold_repetition() || position.fifty_move_draw())
        {
            self.depth += 1;
            node = node.most_promising_child();
            position.make_legal(node.action().unwrap())
        }
        node
    }

    fn expand(&self, node: Arc<Node>, position: &mut Position) -> Arc<Node> {
        if position.threefold_repetition() || position.fifty_move_draw() {
            return node;
        }
        Node::init_children(node.clone(), position);
        if let Some(node) = node.add_child() {
            self.current_nodes.fetch_add(1, Ordering::Relaxed);
            position.make_legal(node.action().unwrap());
            node
        } else {
            node
        }
    }

    fn playout(position: &mut Position) -> f32 {
        let mut actions_played = 0;
        let value = loop {
            if position.fifty_move_draw() || position.threefold_repetition() {
                break 0.;
            }

            let (actions, check) = position.actions();
            if let Some(action) = actions.choose(&mut thread_rng()) {
                position.make_legal(*action);
                actions_played += 1;
            } else {
                break if check && actions_played % 2 == 0 {
                    -1.
                } else if check {
                    -1.
                } else {
                    0.
                };
            }
        };

        for _ in 0..=actions_played {
            position.unmake()
        }
        value
    }

    fn backup(node: Arc<Node>, mut delta: f32, position: &mut Position) {
        let mut current_node = Some(node);
        delta = -delta;
        while let Some(node) = current_node.take() {
            node.modify_score(delta);
            delta = -delta;
            current_node = node.parent();
            position.unmake()
        }
    }

    fn send_info(&self) -> std::io::Result<()> {
        self.writer
            .lock()
            .unwrap()
            .send_message(UciMessage::Information(vec![
                UciInformation::SearchDepth(self.depth),
                UciInformation::SearchTime(self.start_time.elapsed()),
                UciInformation::SearchedNodes(self.current_nodes.load(Ordering::Relaxed)),
                UciInformation::CurrentlySearchedMove {
                    move_index: None,
                    mv: self
                        .root
                        .most_promising_child()
                        .action()
                        .unwrap()
                        .downgrade(),
                },
                UciInformation::PrincipalVariation {
                    ranking: None,
                    moves: self
                        .root
                        .principal_variation()
                        .into_iter()
                        .map(|a| a.downgrade())
                        .collect(),
                },
                UciInformation::CentipawnScore {
                    centipawns: (self.root.exploitation_score() * 1000.) as i16,
                    is_upper_bound: None,
                },
            ]))
    }

    fn send_current_line(&self) -> std::io::Result<()> {
        Ok(())
    }
}
