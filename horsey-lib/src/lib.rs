/*
Horsey, a chess engine that doubles as a chess library.
Copyright (C) 2025 Rautureau Aloïs

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Affero General Public License as published
by the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Affero General Public License for more details.

You should have received a copy of the GNU Affero General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

//! # Horsey
//! A chess engine based on Monte-Carlo Tree Search and
//! NNUE evaluation.
//!
//! It is usable as both a library to embed into your own projects and a standalone
//! binary for analysis or competitions.
//!
#![feature(portable_simd)]

#[cfg(feature = "brain")]
pub mod brain;
pub mod chess;
#[cfg(feature = "epd")]
pub mod epd;
pub mod parsing;
#[cfg(feature = "pgn")]
pub mod pgn;
#[cfg(feature = "search")]
pub mod search;
#[cfg(feature = "uci")]
pub mod uci;
