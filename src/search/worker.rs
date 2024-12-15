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
    brain::nnue::{self, NnueAccumulator},
    game::{action::LegalAction, colour::Colour, position::Position, score::*},
    uci::{
        commands::{UciInformation, UciMessage},
        endpoint::UciWriter,
    },
};

use super::node::{Node, Value};

pub struct MctsWorker<O: Write> {
    pub id: u32,
    pub root: Arc<Node>,
    pub reached_depth: u8,
    pub max_depth: u8,
    pub depth: u8,
    pub perspective: Colour,

    // Search budget
    pub max_duration: Duration,
    pub start_time: Instant,
    pub max_nodes: u64,
    pub current_nodes: Arc<AtomicU64>,
    pub should_stop: Arc<AtomicBool>,

    // Policy
    pub accumulator: NnueAccumulator<'static>,

    // Output to UCI
    pub writer: Arc<Mutex<UciWriter<O>>>,
}
impl<O: Write> MctsWorker<O> {
    /// Creates a new [`MctsWorker`] with no search limits.
    pub fn init(
        id: u32,
        root: Arc<Node>,
        current_nodes: Arc<AtomicU64>,
        should_stop: Arc<AtomicBool>,
        writer: Arc<Mutex<UciWriter<O>>>,
    ) -> Self {
        Self {
            id,
            root,
            current_nodes,
            should_stop,
            writer,
            perspective: Colour::White,
            reached_depth: 0,
            max_depth: u8::MAX,
            depth: 0,
            max_duration: Duration::MAX,
            start_time: Instant::now(),
            max_nodes: u64::MAX,
            accumulator: nnue::get_accumulator(),
        }
    }

    /// Sets the maximum depth this worker is allowed to search.
    pub fn with_max_depth(mut self, depth: u8) -> Self {
        self.max_depth = depth;
        self
    }

    /// Sets the maximum duration for which this worker is allowed to search.
    pub fn with_max_duration(mut self, duration: Duration) -> Self {
        self.max_duration = duration;
        self
    }

    /// Sets the number of nodes after which this worker should stop searching.
    pub fn with_max_nodes(mut self, nodes: u64) -> Self {
        self.max_nodes = nodes;
        self
    }

    /// Runs the search on this worker's search tree.
    pub fn search(mut self, mut position: Position) {
        self.perspective = position.side_to_move();
        let mut info_tick = Instant::now();
        while self.within_budget() {
            self.depth = 0;
            let (selected, expandable) = self.select(self.root.clone(), &mut position);
            let reward = if expandable {
                let expanded = self.expand(selected.clone(), &mut position);
                let reward = self.playout(&mut position);
                expanded.update_value(reward);
                reward
            } else {
                if position.fifty_move_draw() || position.threefold_repetition() {
                    Value::Draw
                } else {
                    let (actions, check) = position.actions();
                    if actions.is_empty() && check {
                        Value::Win(position.side_to_move().inverse())
                    } else if actions.is_empty() {
                        Value::Draw
                    } else {
                        selected.value()
                    }
                }
            };
            Self::backup(selected, reward, &mut position);
            // let _reward = nnue::forward(&self.accumulator, position.side_to_move());

            if self.depth > self.reached_depth {
                self.reached_depth = self.depth
            }

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
            if let Some(m) = self.root.best_move() {
                self.writer
                    .lock()
                    .unwrap()
                    .send_message(UciMessage::SearchResult {
                        best: m.downgrade(),
                        ponder_on: None,
                    })
                    .unwrap()
            }
        }
    }

    /// Checks if this worker is within its search budget.
    pub fn within_budget(&self) -> bool {
        !self.should_stop.load(Ordering::Relaxed)
            && (self.start_time.elapsed() < self.max_duration)
            && (self.current_nodes.load(Ordering::Relaxed) <= self.max_nodes)
            && (self.depth <= self.max_depth)
    }

    /// Selects the most promising leaf node.
    fn select(&mut self, mut node: Arc<Node>, position: &mut Position) -> (Arc<Node>, bool) {
        while node.is_fully_expanded() {
            self.depth += 1;
            let Some(child) = node.most_promising_child() else {
                return (node, false);
            };
            node = child.clone();
            // node.add_virtual_loss();
            position.make_legal(node.action().unwrap());
        }
        (node, true)
    }

    fn expand(&self, node: Arc<Node>, position: &mut Position) -> Arc<Node> {
        Node::init_children(node.clone(), position);
        if let Some(node) = node.add_child() {
            self.current_nodes.fetch_add(1, Ordering::Relaxed);
            position.make_legal(node.action().unwrap());
            node
        } else {
            node
        }
    }

    fn playout(&self, position: &mut Position) -> Value {
        let original = position.clone();
        let value = loop {
            if position.fifty_move_draw() || position.threefold_repetition() {
                break Value::Draw;
            }

            let (actions, check) = position.actions();
            if let Some(action) = actions.choose(&mut thread_rng()) {
                position.make_legal(*action);
            } else {
                break if check {
                    Value::Win(position.side_to_move().inverse())
                } else {
                    Value::Draw
                };
            }
        };

        *position = original;
        value
    }

    fn backup(node: Arc<Node>, value: Value, position: &mut Position) {
        let mut current_node = Some(node);
        while let Some(node) = current_node.take() {
            // node.remove_virtual_loss();
            node.update_value(value);
            current_node = node.parent();
            position.unmake()
        }
    }

    fn send_info(&self) -> std::io::Result<()> {
        let mut informations = vec![
            UciInformation::SearchDepth(self.reached_depth),
            UciInformation::SearchTime(self.start_time.elapsed()),
            UciInformation::SearchedNodes(self.current_nodes.load(Ordering::Relaxed)),
            UciInformation::CurrentlySearchedMove {
                move_index: None,
                mv: self
                    .root
                    .most_promising_child()
                    .unwrap()
                    .action()
                    .unwrap()
                    .downgrade(),
            },
            UciInformation::CentipawnScore {
                centipawns: win_probability_to_centipawns(
                    self.root.value().exploitation_score(self.perspective),
                ),
                is_upper_bound: None,
            },
            UciInformation::SearchSpeed(
                (self.current_nodes.load(Ordering::Relaxed) as f32
                    / self.start_time.elapsed().as_secs_f32()) as u64,
            ),
        ];
        let pv: Vec<_> = self
            .root
            .principal_variation()
            .into_iter()
            .map(LegalAction::downgrade)
            .collect();
        if !pv.is_empty() {
            informations.push(UciInformation::PrincipalVariation {
                ranking: None,
                moves: pv,
            })
        }

        self.writer
            .lock()
            .unwrap()
            .send_message(UciMessage::Information(informations))
    }

    fn send_current_line(&self) -> std::io::Result<()> {
        Ok(())
    }
}
