//! # UCI search options

use std::{
    num::{NonZeroU64, NonZeroU8},
    time::Duration,
};

use crate::game::action::Action;

/// A builder to create clean parameters of search from the server to the engine.
#[derive(Clone, PartialEq, Eq, Default, Debug)]
pub struct UciSearchParameters {
    pub(crate) available_moves: Vec<Action>,
    pub(crate) ponder: bool,
    pub(crate) white_time: Option<Duration>,
    pub(crate) black_time: Option<Duration>,
    pub(crate) white_increment: Option<Duration>,
    pub(crate) black_increment: Option<Duration>,
    pub(crate) moves_until_time_control: Option<NonZeroU8>,
    pub(crate) depth: Option<NonZeroU8>,
    pub(crate) nodes: Option<NonZeroU64>,
    pub(crate) distance_to_mate: Option<NonZeroU8>,
    pub(crate) search_time: Option<Duration>,
    pub(crate) infinite: bool,
}
impl UciSearchParameters {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn with_available_moves(mut self, moves: &[Action]) -> Self {
        self.available_moves = Vec::from(moves);
        self
    }
    pub fn set_ponder(mut self, ponder: bool) -> Self {
        self.ponder = ponder;
        self
    }
    pub fn with_time_constraint(mut self, time: Duration) -> Self {
        self.white_time = if time.is_zero() { None } else { Some(time) };
        self
    }
    pub fn with_white_time(mut self, time: Duration) -> Self {
        self.black_time = if time.is_zero() { None } else { Some(time) };
        self
    }
    pub fn with_black_time(mut self, time: Duration) -> Self {
        self.black_time = if time.is_zero() { None } else { Some(time) };
        self
    }
    pub fn with_white_increment(mut self, increment: Duration) -> Self {
        self.white_increment = if increment.is_zero() {
            None
        } else {
            Some(increment)
        };
        self
    }
    pub fn with_black_increment(mut self, increment: Duration) -> Self {
        self.black_increment = if increment.is_zero() {
            None
        } else {
            Some(increment)
        };
        self
    }
    pub fn with_moves_until_time_control(mut self, moves: u8) -> Self {
        if let Some(moves) = NonZeroU8::new(moves) {
            self.moves_until_time_control = Some(moves)
        } else {
            self.moves_until_time_control = None
        }
        self
    }
    pub fn with_depth(mut self, depth: u8) -> Self {
        if let Some(depth) = NonZeroU8::new(depth) {
            self.depth = Some(depth)
        } else {
            self.depth = None
        }
        self
    }
    pub fn with_nodes(mut self, nodes: u64) -> Self {
        if let Some(nodes) = NonZeroU64::new(nodes) {
            self.nodes = Some(nodes)
        } else {
            self.nodes = None
        }
        self
    }
    pub fn with_distance_to_mate(mut self, distance: u8) -> Self {
        if let Some(distance) = NonZeroU8::new(distance) {
            self.distance_to_mate = Some(distance)
        } else {
            self.distance_to_mate = None
        }
        self
    }
    pub fn with_search_time(mut self, time: Duration) -> Self {
        self.search_time = if time.is_zero() { None } else { Some(time) };
        self
    }
    pub fn set_infinite(mut self, infinite: bool) -> Self {
        self.infinite = infinite;
        self
    }

    pub fn as_uci_string(&self) -> String {
        let mut uci = String::new();
        if !self.available_moves.is_empty() {
            uci = format!(
                "{uci}searchmoves {} ",
                self.available_moves
                    .iter()
                    .fold(String::new(), |acc, m| format!("{acc} {m}"))
            )
        }
        if self.ponder {
            uci = format!("{uci}ponder ")
        }
        if let Some(time) = self.white_time {
            uci = format!("{uci}wtime {} ", time.as_millis())
        }
        if let Some(time) = self.black_time {
            uci = format!("{uci}btime {} ", time.as_millis())
        }
        if let Some(increment) = self.white_increment {
            uci = format!("{uci}winc {} ", increment.as_millis())
        }
        if let Some(increment) = self.black_increment {
            uci = format!("{uci}binc {} ", increment.as_millis())
        }
        if let Some(moves) = self.moves_until_time_control {
            uci = format!("{uci}movestogo {moves} ")
        }
        if let Some(depth) = self.depth {
            uci = format!("{uci}depth {depth} ")
        }
        if let Some(nodes) = self.nodes {
            uci = format!("{uci}nodes {nodes} ")
        }
        if let Some(distance) = self.distance_to_mate {
            uci = format!("{uci}mate {distance} ")
        }
        if let Some(search_time) = self.search_time {
            uci = format!("{uci}movetime {} ", search_time.as_millis())
        }
        if self.infinite {
            uci = format!("{uci}infinite")
        }
        uci
    }
}
impl std::fmt::Display for UciSearchParameters {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_uci_string())
    }
}
