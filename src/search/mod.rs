//! # Search algorithm implementation

use std::{
    io::Write,
    sync::{
        atomic::{AtomicBool, AtomicU64, Ordering},
        Arc, Mutex,
    },
    thread::JoinHandle,
    time::Duration,
};

use node::{Node, Value};
use worker::MctsWorker;

use crate::{
    chess::{
        action::{Action, UciMove},
        position::Position,
    },
    uci::{endpoint::UciWriter, search::UciSearchParameters},
};

mod node;
mod worker;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SearchConfig {
    max_duration: (Duration, Duration),
    max_depth: u8,
    actions: Vec<UciMove>,
    max_nodes: u64,
    threads: u32,
    search_mate: bool,
}
impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            max_duration: (Duration::MAX, Duration::MAX),
            max_depth: u8::MAX,
            max_nodes: u64::MAX,
            actions: vec![],
            threads: num_cpus::get_physical() as u32,
            search_mate: false,
        }
    }
}
impl SearchConfig {
    /// Creates a new search configuration with no limitations and as many threads
    /// as there are available physical CPU cores.
    pub fn new() -> Self {
        Self::default()
    }

    /// Changes the maximum duration of the search.
    ///
    /// Note that this overrides the value set with [`SearchConfig::with_time_constraints`].
    pub fn with_max_duration(mut self, duration: Duration) -> Self {
        self.max_duration = (duration, duration);
        self
    }

    fn compute_time_constraint(
        white_time: Duration,
        black_time: Duration,
        white_increment: Option<Duration>,
        black_increment: Option<Duration>,
        moves_before_time_control: Option<u8>,
    ) -> (Duration, Duration) {
        // TODO: this is naive, should upgrade someday
        const EXPECTED_GAME_DURATION: u8 = 64;

        let total_white_time = white_time + white_increment.unwrap_or(Duration::ZERO);
        let total_black_time = black_time + black_increment.unwrap_or(Duration::ZERO);

        let black_max_allocated = black_time.as_secs_f32()
            / (moves_before_time_control.unwrap_or(EXPECTED_GAME_DURATION) + 1) as f32;
        let white_max_allocated = white_time.as_secs_f32()
            / (moves_before_time_control.unwrap_or(EXPECTED_GAME_DURATION) + 1) as f32;

        let black_time_disadvantage =
            total_black_time.as_secs_f32() / total_white_time.as_secs_f32();
        let white_time_disadvantage =
            total_white_time.as_secs_f32() / total_black_time.as_secs_f32();

        let black_time = Duration::from_secs_f32(black_max_allocated * black_time_disadvantage)
            .min(Duration::from_secs(10));
        let white_time = Duration::from_secs_f32(white_max_allocated * white_time_disadvantage)
            .min(Duration::from_secs(10));
        (black_time, white_time)
    }

    /// Computes the appropriate search duration given time constraints for both sides.
    ///
    /// Note that this overrides the value set with [`SearchConfig::with_max_duration`].
    pub fn with_time_constraints(
        mut self,
        white_time: Duration,
        black_time: Duration,
        white_increment: Option<Duration>,
        black_increment: Option<Duration>,
        moves_before_time_control: Option<u8>,
    ) -> Self {
        self.max_duration = Self::compute_time_constraint(
            white_time,
            black_time,
            white_increment,
            black_increment,
            moves_before_time_control,
        );
        self
    }

    /// Sets the maximum depth that the search can reach before returning a result.
    pub fn with_max_depth(mut self, depth: u8) -> Self {
        self.max_depth = depth;
        self
    }

    /// Sets the maximum number of nodes that the search can explore before returning a result.
    pub fn with_max_nodes(mut self, nodes: u64) -> Self {
        self.max_nodes = nodes;
        self
    }

    /// Sets a list of actions that the search should limit itself to.
    ///
    /// Any non-legal action present in the list will be ignored.
    pub fn actions_to_search(mut self, actions: &[UciMove]) -> Self {
        self.actions = Vec::from(actions);
        self
    }

    /// Sets the number of worker threads that the search should use.
    ///
    /// Setting this number to more than there are CPU cores on your system might
    /// be detrimental to performance.
    pub fn with_workers(mut self, workers: u32) -> Self {
        self.threads = workers.max(1);
        self
    }

    /// Runs a search given the previously set parameters.
    pub fn go<O: Write + Send + 'static>(
        self,
        position: Position,
        writer: Arc<Mutex<UciWriter<O>>>,
    ) -> SearchHandle {
        let root = Node::new_root(position.side_to_move());
        let current_nodes = Arc::new(AtomicU64::new(0));
        let should_stop = Arc::new(AtomicBool::new(false));
        let workers = (0u32..self.threads)
            .map(|id| {
                let root = root.clone();
                let position = position.clone();
                let should_stop = should_stop.clone();
                let current_nodes = current_nodes.clone();
                let writer = writer.clone();
                std::thread::spawn(move || {
                    MctsWorker::init(id, root, current_nodes, should_stop, writer)
                        .with_max_depth(self.max_depth)
                        .with_max_duration(if position.side_to_move().is_black() {
                            self.max_duration.0
                        } else {
                            self.max_duration.1
                        })
                        .with_max_nodes(self.max_nodes)
                        .search(position);
                })
            })
            .collect();

        SearchHandle {
            should_stop,
            root,
            workers,
        }
    }
}
impl From<UciSearchParameters> for SearchConfig {
    fn from(value: UciSearchParameters) -> Self {
        let mut config = Self::new();
        if value.distance_to_mate.is_some() {
            config.search_mate = true;
        }
        config.actions = value.available_moves;

        if !value.infinite {
            if let Some(depth) = value.depth {
                config.max_depth = depth.get()
            }
            if let Some(mate) = value.distance_to_mate {
                config.max_depth = mate.get()
            }
            if let Some(nodes) = value.nodes {
                config.max_nodes = nodes.get()
            }

            if let Some(search_time) = value.search_time {
                config.max_duration = (search_time, search_time)
            } else if let Some(white_time) = value.white_time {
                config.max_duration = Self::compute_time_constraint(
                    white_time,
                    value.black_time.unwrap_or(Duration::MAX),
                    value.white_increment,
                    value.black_increment,
                    value.moves_until_time_control.map(|m| m.get()),
                )
            } else if let Some(black_time) = value.black_time {
                config.max_duration = Self::compute_time_constraint(
                    value.white_time.unwrap_or(Duration::MAX),
                    black_time,
                    value.white_increment,
                    value.black_increment,
                    value.moves_until_time_control.map(|m| m.get()),
                )
            }
        }

        // TODO: handle pondering

        config
    }
}
impl From<&UciSearchParameters> for SearchConfig {
    fn from(value: &UciSearchParameters) -> Self {
        Self::from(value.clone())
    }
}
impl std::fmt::Display for SearchConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.search_mate {
            write!(f, "[mate search] ")?
        }
        if self.max_depth != u8::MAX {
            write!(f, "max depth: {}, ", self.max_depth)?
        }
        if self.max_duration.0 != Duration::MAX {
            write!(
                f,
                "max black duration: {}s, ",
                self.max_duration.0.as_secs_f32()
            )?
        }
        if self.max_duration.1 != Duration::MAX {
            write!(
                f,
                "max white duration: {}s, ",
                self.max_duration.1.as_secs_f32()
            )?
        }
        if self.max_nodes != u64::MAX {
            write!(f, "max nodes: {}, ", self.max_nodes)?
        }
        if !self.actions.is_empty() {
            write!(f, "available actions: ")?;
            for action in &self.actions {
                write!(f, "{action} ")?
            }
            write!(f, ", ")?
        }
        write!(f, "workers: {}", self.threads)
    }
}

/// Handle to an ongoing search.
pub struct SearchHandle {
    should_stop: Arc<AtomicBool>,
    root: Arc<Node>,
    workers: Vec<JoinHandle<()>>,
}
impl SearchHandle {
    /// Stops the search.
    pub fn stop(&mut self) {
        self.should_stop.store(true, Ordering::Relaxed);

        for worker in self.workers.drain(0..self.workers.len()) {
            worker.join().unwrap();
        }
    }

    /// Wait for workers to finish their search.
    pub fn wait(&mut self) {
        for worker in self.workers.drain(0..self.workers.len()) {
            worker.join().unwrap();
        }
    }

    /// Returns the search's current best action.
    pub fn best_action(&self) -> Option<Action> {
        self.root.best_move()
    }

    /// Returns the search's current principal variation i.e. the expected best
    /// sequence of moves.
    ///
    /// When running a forced checkmate search, this only returns [`Some`] when a mate is found.
    pub fn principal_variation(&self) -> Option<Vec<Action>> {
        Some(self.root.principal_variation())
    }

    pub fn value(&self) -> Value {
        self.root.value()
    }
}
