//! # Horsey
//! A chess engine based on Monte-Carlo Tree Search and
//! NNUE evaluation.
//!
//! It is usable as both a library to embed into your own projects and a standalone
//! binary for analysis or competitions.
#![feature(portable_simd)]

pub mod brain;
pub mod chess;
pub mod search;
pub mod uci;
