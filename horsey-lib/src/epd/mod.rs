//! # Extended Position Description format
//! A chess position text format similar to FEN, but designed to be expandable
//! using *operations*.
//!
//! EPD is usually meant for representing engine test suites of positions annotated
//! with best move indications.

use operation::EpdOperation;

use crate::{
    chess::{
        bitboard::*,
        castling_rights::CastlingRights,
        colour::*,
        fen::{Fen, FenParseError},
        piece::*,
        square::File,
    },
    parsing::{PartialFromStr, parse_char},
};

pub mod operation;

/// An Extended Position Description contains:
/// - piece placement
/// - side to move
/// - castling rights
/// - en passant target square (if any)
/// - a list of [`EpdOperation`]
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub struct Epd {
    pub(crate) bitboards: [Bitboard; NUM_COLOURS + NUM_PIECES],
    pub side_to_move: Colour,
    pub castling_rights: CastlingRights,
    pub en_passant_file: Option<File>,
    pub operations: Vec<EpdOperation>,
}
impl PartialFromStr for Epd {
    type Err = FenParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let (fen, s) = Fen::partial_from_str(s)?;

        let mut operations = vec![];
        let s = if let Ok(mut s) = parse_char(s, ' ') {
            while let Ok((op, left)) = EpdOperation::partial_from_str(s) {
                operations.push(op);
                if let Ok(left) = parse_char(left, ' ') {
                    s = left
                } else {
                    s = left;
                    break;
                }
            }
            s
        } else {
            s
        };

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
impl std::str::FromStr for Epd {
    type Err = FenParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(epd, rest)| {
            if rest.is_empty() {
                Ok(epd)
            } else {
                Err(FenParseError::InputTooLong)
            }
        })
    }
}
