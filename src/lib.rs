//! # Chameleon-chess
//! A chess engine based on the `chameleon` general game playing framework and
//! NNUE evaluation.
//!
//! It is usable as both a library to embed into your own projects and a standalone
//! binary for analysis or competitions.

pub mod bitboard;
pub mod r#move;
pub mod position;
pub mod square;

#[cfg(test)]
mod tests;
