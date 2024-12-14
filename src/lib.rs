//! # Chameleon-chess
//! A chess engine based on the `chameleon` general game playing framework and
//! NNUE evaluation.
//!
//! It is usable as both a library to embed into your own projects and a standalone
//! binary for analysis or competitions.

pub mod board;
pub mod brain;
pub mod protocols;
pub mod search;
