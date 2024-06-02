//! Protocols are used to communicate with the chess engine from other programs (Chess GUIs, tournaments, APIs, etc).
//!
//! chameleon-chess implements the most common ones:
//! - Universal Chess Interface (UCI)
//! - Chess Engine Communication Protocol (CECP)

pub mod cecp;
pub mod uci;
