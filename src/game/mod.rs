//! # Chess API
//! This module contains everything Chess related, like the board state, actions,
//! scoring, etc.

pub mod action;
mod bitboard;
pub mod castling_rights;
pub mod colour;
mod history;
mod magic_tables;
// pub mod opening;
#[cfg(feature = "perft")]
pub mod perft;
pub mod piece;
pub mod position;
pub mod score;
pub mod square;
mod zobrist;
