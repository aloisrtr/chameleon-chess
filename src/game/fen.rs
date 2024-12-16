//! # FEN string utilities

use crate::game::square::Rank;

use super::{
    bitboard::Bitboard,
    castling_rights::CastlingRights,
    colour::{Colour, NUM_COLOURS},
    piece::{PieceKind, NUM_PIECES},
    square::Square,
};
use bitstream_io::{BitRead, BitWrite};
use thiserror::Error;

#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Error)]
// TODO: Better FEN parsing error reports.
/// FEN parsing errors.
pub enum FenError {
    #[error("Unexpected character at index {index}: {val}")]
    UnexpectedToken { index: usize, val: char },
    #[error("FEN string missing the {0} section")]
    Incomplete(&'static str),
    #[error("Found a non-ASCII character")]
    NonAscii,
    #[error("Failed to parse")]
    ParseError,
    #[error("Piece section only defines {0} squares out of 8")]
    IncompletePieceSection(u8),
    #[error("The piece section defines too many squares")]
    TooManySquares,
}

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
    pub fn parse(fen: &str) -> Result<Self, FenError> {
        fen.parse()
    }

    /// Returns the piece kind and colour on a given square if any.
    pub fn piece_on(&self, square: Square) -> Option<(PieceKind, Colour)> {
        let sq_bb = square.bitboard();

        for kind in PieceKind::iter() {
            if self.bitboards[kind as usize + 2].intersects(sq_bb) {
                if self.bitboards[Colour::White as usize].intersects(sq_bb) {
                    return Some((kind, Colour::White));
                } else {
                    return Some((kind, Colour::Black));
                }
            }
        }

        None
    }

    /// Compresses a FEN string for efficient storage.
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
impl std::str::FromStr for Fen {
    type Err = FenError;

    fn from_str(fen_str: &str) -> Result<Self, Self::Err> {
        if !fen_str.is_ascii() {
            return Err(FenError::NonAscii);
        }

        let mut bitboards = [Bitboard::empty(); 8];
        let sections = fen_str.split_ascii_whitespace().collect::<Vec<_>>();
        let pieces_str = sections.first().ok_or(FenError::Incomplete("pieces"))?;
        let mut squares = Square::squares_fen_iter();
        for c in pieces_str.chars() {
            let colour = if c.is_ascii_lowercase() {
                Colour::Black
            } else {
                Colour::White
            };
            match c.to_ascii_lowercase() {
                'p' => {
                    let sq_bb = squares.next().ok_or(FenError::TooManySquares)?.bitboard();
                    bitboards[PieceKind::Pawn as usize + 2] |= sq_bb;
                    bitboards[colour as usize] |= sq_bb;
                }
                'n' => {
                    let sq_bb = squares.next().ok_or(FenError::TooManySquares)?.bitboard();
                    bitboards[PieceKind::Knight as usize + 2] |= sq_bb;
                    bitboards[colour as usize] |= sq_bb;
                }
                'b' => {
                    let sq_bb = squares.next().ok_or(FenError::TooManySquares)?.bitboard();
                    bitboards[PieceKind::Bishop as usize + 2] |= sq_bb;
                    bitboards[colour as usize] |= sq_bb;
                }
                'r' => {
                    let sq_bb = squares.next().ok_or(FenError::TooManySquares)?.bitboard();
                    bitboards[PieceKind::Rook as usize + 2] |= sq_bb;
                    bitboards[colour as usize] |= sq_bb;
                }
                'q' => {
                    let sq_bb = squares.next().ok_or(FenError::TooManySquares)?.bitboard();
                    bitboards[PieceKind::Queen as usize + 2] |= sq_bb;
                    bitboards[colour as usize] |= sq_bb;
                }
                'k' => {
                    let sq_bb = squares.next().ok_or(FenError::TooManySquares)?.bitboard();
                    bitboards[PieceKind::King as usize + 2] |= sq_bb;
                    bitboards[colour as usize] |= sq_bb;
                }
                '/' => continue,
                digit if digit.is_ascii_digit() => {
                    let skip = digit.to_digit(10).unwrap() as usize;
                    if skip > 8 {
                        return Err(FenError::UnexpectedToken {
                            index: 0,
                            val: digit,
                        });
                    }
                    for _ in 0..skip {
                        squares.next();
                    }
                }
                c => return Err(FenError::UnexpectedToken { index: 0, val: c }),
            }
        }

        let side_to_move = match *sections
            .get(1)
            .ok_or(FenError::Incomplete("Side to move"))?
        {
            "w" => Colour::White,
            "b" => Colour::Black,
            _ => return Err(FenError::UnexpectedToken { index: 0, val: '0' }),
        };

        let castling_rights = sections
            .get(2)
            .ok_or(FenError::Incomplete("Castling rights"))?
            .parse()
            .map_err(|_| FenError::ParseError)?;

        let en_passant = match *sections.get(3).ok_or(FenError::Incomplete("En passant"))? {
            "-" => None,
            s => Some(s.parse::<Square>().map_err(|_| FenError::ParseError)?),
        };

        let halfmove_clock = sections.get(4).unwrap_or(&"0").parse().unwrap();
        let fullmove_counter = sections.get(5).unwrap_or(&"1").parse().unwrap();

        Ok(Self {
            bitboards,
            side_to_move,
            castling_rights,
            en_passant,
            halfmove_clock,
            fullmove_counter,
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
        for sq in Square::squares_fen_iter() {
            if let Some((piece, colour)) = self.piece_on(sq) {
                if skip != 0 {
                    write!(f, "{skip}")?;
                    skip = 0
                }
                let mut p = match piece {
                    PieceKind::Pawn => 'p',
                    PieceKind::Knight => 'n',
                    PieceKind::Bishop => 'b',
                    PieceKind::Rook => 'r',
                    PieceKind::Queen => 'q',
                    PieceKind::King => 'k',
                };
                if colour == Colour::White {
                    p = p.to_ascii_uppercase();
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

        write!(
            f,
            "{} {} {} {} {}",
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
    use std::io::Cursor;

    use bitstream_io::{BigEndian, BitReader, BitWriter};

    use super::*;

    #[test]
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
