//! # Core Chess API
//! This module contains everything Chess related such as the board state, actions,
//! scoring, etc.

pub mod action;
pub(crate) mod bitboard;
pub mod castling_rights;
pub mod colour;
mod history;
mod magic_tables;
pub mod perft;
pub mod piece;
pub mod position;
pub mod score;
pub mod square;
mod zobrist;

pub mod fen;
