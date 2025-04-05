//! # Forsyth-Edwards Notation (FEN) utilities.
//!
//! Allows parsing, formatting and provides a clean API over FEN strings.
//!
//! ## Compression/Decompression
//! The `serde` feature allows for streaming compression/decompression capabilities. These
//! algorithms are made much more efficient if running on a CPU with BMI2 expansion, but
//! will work on any CPU.

use crate::{
    chess::square::Rank,
    parsing::{PartialFromStr, parse_int, walk_whitespace},
};

use super::{
    bitboard::Bitboard,
    castling_rights::CastlingRights,
    colour::{Colour, NUM_COLOURS},
    piece::{NUM_PIECES, Piece, PieceKind},
    square::Square,
};

#[cfg(feature = "serde")]
use bitstream_io::{BitRead, BitWrite};
use thiserror::Error;

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Error)]
// TODO: Better FEN parsing error reports.
/// FEN parsing errors with context.
pub enum FenError {
    /// A section contained an unexpected character.
    #[error("Unexpected character at index {index}: {val}")]
    UnexpectedToken { index: usize, val: char },
    /// A necessary section of the FEN string was missing.
    #[error("FEN string missing the {0} section")]
    Incomplete(&'static str),
    /// A non-ASCII character was found.
    #[error("Found a non-ASCII character")]
    NonAscii,
    /// The piece section of the FEN string did not define all squares.
    #[error("Piece section only defines {0} squares out of 8")]
    IncompletePieceSection(u8),
    /// Too many squares were defined in the FEN string.
    #[error("The piece section defines too many squares")]
    TooManySquares,
    /// Indicates a generic parse error (fallback case).
    #[error("Failed to parse")]
    ParseError,
}

/// FEN string representation.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Fen {
    pub(crate) bitboards: [Bitboard; NUM_COLOURS + NUM_PIECES],
    pub side_to_move: Colour,
    pub castling_rights: CastlingRights,
    pub en_passant: Option<Square>,
    pub halfmove_clock: u16,
    pub fullmove_counter: u16,
}
impl Fen {
    /// Parses a FEN string.
    /// # Example
    /// ```
    /// # use horsey::chess::fen::*;
    /// # use horsey::chess::castling_rights::*;
    /// # use horsey::chess::colour::*;
    /// let initial_position_fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
    /// let parsed_values = Fen::parse(initial_position_fen).unwrap();
    /// assert_eq!(parsed_values.side_to_move, Colour::White);
    /// assert_eq!(parsed_values.castling_rights, CastlingRights::full());
    /// ```
    pub fn parse(fen: &str) -> Result<Self, FenError> {
        fen.parse()
    }

    /// Returns the [`PieceKind`] and [`Colour`] of a piece on a given square if any.
    /// # Example
    /// ```
    /// # use horsey::chess::fen::*;
    /// # use horsey::chess::colour::*;
    /// # use horsey::chess::piece::*;
    /// # use horsey::chess::square::*;
    /// let initial_position_fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
    /// let parsed_values = Fen::parse(initial_position_fen).unwrap();
    /// assert_eq!(parsed_values.piece_on(Square::E2), Some(Piece::new(PieceKind::Pawn, Colour::White)));
    pub fn piece_on(&self, square: Square) -> Option<Piece> {
        let sq_bb = square.bitboard();

        for kind in PieceKind::iter() {
            if self.bitboards[kind as usize + 2].intersects(sq_bb) {
                return Some(Piece {
                    kind,
                    colour: self.bitboards[Colour::Black as usize]
                        .intersects(sq_bb)
                        .into(),
                });
            }
        }

        None
    }

    /// Compresses a FEN string for efficient storage.
    #[cfg(feature = "serde")]
    pub fn compress<W: BitWrite>(&self, stream: &mut W) -> std::io::Result<()> {
        let mut rocc =
            self.bitboards[Colour::White as usize] | self.bitboards[Colour::Black as usize];
        stream.write(64, u64::from(rocc))?;
        stream.write(
            rocc.cardinality() as u32,
            u64::from(self.bitboards[Colour::White as usize].pext(rocc)),
        )?;
        for piece in PieceKind::iter_all_but_king() {
            let piece_bb = self.bitboards[piece as usize + 2];
            stream.write(rocc.cardinality() as u32, u64::from(piece_bb.pext(rocc)))?;
            rocc ^= piece_bb;
        }
        debug_assert_eq!(rocc, self.bitboards[PieceKind::King as usize + 2]);

        stream.write_bit(self.side_to_move.is_black())?;

        stream.write_bit(self.en_passant.is_some())?;
        let white_candis = (self.bitboards[Colour::White as usize]
            & self.bitboards[PieceKind::Pawn as usize + 2]
            & Rank::Four.bitboard())
            << 8;
        let black_candis = (self.bitboards[Colour::Black as usize]
            & self.bitboards[PieceKind::Pawn as usize + 2]
            & Rank::Six.bitboard())
            >> 8;
        let candis = white_candis | black_candis;
        stream.write(
            candis.cardinality() as u32,
            u64::from(
                self.en_passant
                    .map(|ep_square| ep_square.bitboard())
                    .unwrap_or(Bitboard::empty())
                    .pext(candis),
            ),
        )?;

        let rooks = self.bitboards[PieceKind::Rook as usize + 2];
        let castler = self.castling_rights.castle_mask() & rooks;
        stream.write(rooks.cardinality() as u32, u64::from(castler.pext(rooks)))?;

        stream.write(7, self.halfmove_clock)
    }

    /// Decompresses a FEN string from a packed storage.
    #[cfg(feature = "serde")]
    pub fn decompress<R: BitRead>(stream: &mut R) -> std::io::Result<Self> {
        let mut bitboards = [Bitboard::empty(); 8];

        let mut rocc: Bitboard = stream.read::<u64>(64)?.into();
        let bb_white: Bitboard =
            Bitboard::from(stream.read::<u64>(rocc.cardinality() as u32)?).pdep(rocc);
        bitboards[Colour::White as usize] = bb_white;
        bitboards[Colour::Black as usize] = bb_white ^ rocc;

        for kind in PieceKind::iter_all_but_king() {
            let piece_bb =
                Bitboard::from(stream.read::<u64>(rocc.cardinality() as u32)?).pdep(rocc);
            rocc ^= piece_bb;
            bitboards[kind as usize + 2] = piece_bb;
        }
        bitboards[PieceKind::King as usize + 2] = rocc;
        rocc ^= bitboards[PieceKind::King as usize + 2];
        debug_assert_eq!(Bitboard::empty(), rocc);

        let side_to_move = stream.read_bit()?.into();

        let en_passant = if stream.read_bit()? {
            let white_candis = (bitboards[Colour::White as usize]
                & bitboards[PieceKind::Pawn as usize + 2]
                & Rank::Four.bitboard())
                << 8;
            let black_candis = (bitboards[Colour::Black as usize]
                & bitboards[PieceKind::Pawn as usize + 2]
                & Rank::Six.bitboard())
                >> 8;
            let candis = white_candis | black_candis;
            let mut ep_square =
                Bitboard::from(stream.read::<u64>(candis.cardinality() as u32)?).pdep(candis);
            ep_square.pop_lowest_set_square()
        } else {
            None
        };

        let rooks = bitboards[PieceKind::Rook as usize + 2];
        let castlers = Bitboard::from(stream.read::<u64>(rooks.cardinality() as u32)?).pdep(rooks);
        let mut castling_rights = CastlingRights::none();
        if castlers.intersects(Square::H1.bitboard()) {
            castling_rights.allow_kingside_castle(Colour::White)
        }
        if castlers.intersects(Square::H8.bitboard()) {
            castling_rights.allow_kingside_castle(Colour::Black)
        }
        if castlers.intersects(Square::A1.bitboard()) {
            castling_rights.allow_queenside_castle(Colour::White)
        }
        if castlers.intersects(Square::A8.bitboard()) {
            castling_rights.allow_queenside_castle(Colour::Black)
        }

        let halfmove_clock = stream.read(7)?;

        Ok(Fen {
            bitboards,
            side_to_move,
            en_passant,
            castling_rights,
            halfmove_clock,
            fullmove_counter: 1,
        })
    }
}
impl PartialFromStr for Fen {
    type Err = FenError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        fn parse_piece_section(mut s: &str) -> Result<([Bitboard; 8], &str), FenError> {
            let mut bitboards = [Bitboard::empty(); 8];
            let mut ranks = Rank::iter().rev();
            let mut squares = Square::rank_squares_iter(ranks.next().unwrap());
            while let Some(c) = s.chars().next() {
                if let Some(digit) = c.to_digit(10) {
                    for _ in 0..digit {
                        _ = squares.next()
                    }
                    s = &s[1..];
                } else if c == '/' {
                    if squares.next().is_some() {
                        // TODO: better error
                        return Err(FenError::IncompletePieceSection(0));
                    }
                    squares = if let Some(rank) = ranks.next() {
                        Square::rank_squares_iter(rank)
                    } else {
                        // TODO: same here
                        return Err(FenError::ParseError);
                    };

                    s = &s[1..];
                } else if c == ' ' {
                    break;
                } else {
                    let (piece, left) = Piece::partial_from_str(s).unwrap();
                    let square = squares.next().unwrap();
                    bitboards[NUM_COLOURS + piece.kind as usize].set(square);
                    bitboards[piece.colour as usize].set(square);
                    s = left
                }
            }

            if squares.next().is_some() {
                Err(FenError::Incomplete("Piece placement"))
            } else {
                Ok((bitboards, s))
            }
        }

        let (bitboards, s) = parse_piece_section(s)?;

        let s = walk_whitespace(s);
        let side_to_move = match s.chars().next() {
            Some('w') => Colour::White,
            Some('b') => Colour::Black,
            _ => Err(FenError::Incomplete("Side to play"))?,
        };
        let s = &s[1..];

        // TODO: handle error
        let (castling_rights, s) = CastlingRights::partial_from_str(walk_whitespace(s)).unwrap();

        let s = walk_whitespace(s);
        let (en_passant, s) = match s.chars().next() {
            Some('-') => (None, &s[1..]),
            Some(_) => {
                // TODO error invalid ep square
                let (sq, s) = Square::partial_from_str(s).unwrap();
                (Some(sq), s)
            }
            None => Err(FenError::Incomplete("En passant target"))?,
        };

        // TODO: check errors here
        let (halfmove_clock, s) = match parse_int(walk_whitespace(s)) {
            Ok((h, s)) => (h, s),
            Err(_) => (0, s),
        };
        let (fullmove_counter, s) = match parse_int(walk_whitespace(s)) {
            Ok((f, s)) => (f, s),
            Err(_) => (0, s),
        };

        Ok((
            Self {
                bitboards,
                side_to_move,
                en_passant,
                castling_rights,
                halfmove_clock,
                fullmove_counter,
            },
            s,
        ))
    }
}
impl std::str::FromStr for Fen {
    type Err = FenError;

    fn from_str(fen_str: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(fen_str).and_then(|(fen, s)| {
            if s.is_empty() {
                Ok(fen)
            } else {
                Err(FenError::ParseError)
            }
        })
    }
}
impl std::fmt::Display for Fen {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::fmt::Debug for Fen {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Pieces
        let mut skip = 0;
        let mut line_length = 0;
        for rank in Rank::iter().rev() {
            for sq in Square::rank_squares_iter(rank) {
                if let Some(p) = self.piece_on(sq) {
                    if skip != 0 {
                        write!(f, "{skip}")?;
                        skip = 0
                    }
                    write!(f, "{p}")?;
                } else {
                    skip += 1
                }

                line_length = (line_length + 1) % 8;
                if line_length == 0 {
                    if skip != 0 {
                        write!(f, "{skip}")?;
                        skip = 0;
                    }
                    if sq.rank() != Rank::One {
                        write!(f, "/")?
                    }
                }
            }
        }

        write!(
            f,
            " {} {} {} {} {}",
            if self.side_to_move.is_black() {
                'b'
            } else {
                'w'
            },
            self.castling_rights,
            if let Some(ep) = self.en_passant {
                ep.to_string()
            } else {
                String::from("-")
            },
            self.halfmove_clock,
            self.fullmove_counter
        )
    }
}

#[cfg(test)]
mod test {
    #[cfg(feature = "serde")]
    use bitstream_io::{BigEndian, BitReader, BitWriter};

    #[cfg(feature = "serde")]
    use super::*;

    #[test]
    #[cfg(feature = "serde")]
    fn compress_decompress_ok() {
        let fen: Fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"
            .parse()
            .unwrap();
        let buffer = [0u8; 64];
        let mut writer = BitWriter::endian(Cursor::new(buffer), BigEndian);
        fen.compress(&mut writer).unwrap();

        let buffer = writer.into_writer().into_inner();
        let mut reader = BitReader::endian(Cursor::new(&buffer), BigEndian);
        let result = Fen::decompress(&mut reader).unwrap();

        assert_eq!(fen, result)
    }
}
