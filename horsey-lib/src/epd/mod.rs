//! # Extended Position Description format
//! A chess position text format similar to FEN, but designed to be expandable
//! using *operations*.
//!
//! EPD is usually meant for representing engine test suites of positions annotated
//! with best move indications.

use operation::EpdOperation;

use crate::{
    chess::{
        bitboard::*, castling_rights::CastlingRights, colour::*, fen::Fen, piece::*, square::File,
    },
    parsing::{PartialFromStr, walk_whitespace},
};

pub mod operation;

/// An Extended Position Description contains:
/// - piece placement
/// - side to move
/// - castling rights
/// - en passant target square (if any)
/// - a list of [`EpdOperation`]
pub struct Epd {
    pub(crate) bitboards: [Bitboard; NUM_COLOURS + NUM_PIECES],
    pub side_to_move: Colour,
    pub castling_rights: CastlingRights,
    pub en_passant_file: Option<File>,
    pub operations: Vec<EpdOperation>,
}
impl PartialFromStr for Epd {
    type Err = ();

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let (fen, s) = Fen::partial_from_str(s).map_err(|_| ())?;

        let mut s = walk_whitespace(s);
        let mut operations = vec![];
        while let Ok((op, left)) = EpdOperation::partial_from_str(s) {
            operations.push(op);
            s = walk_whitespace(left)
        }

        Ok((
            Self {
                bitboards: fen.bitboards,
                side_to_move: fen.side_to_move,
                castling_rights: fen.castling_rights,
                en_passant_file: fen.en_passant_file,
                operations,
            },
            s,
        ))
    }
}
