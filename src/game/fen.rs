//! # FEN string utilities

use crate::game::square::Rank;

use super::{castling_rights::CastlingRights, colour::Colour, piece::PieceKind, square::Square};
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

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct Fen {
    pub pieces: [Option<(PieceKind, Colour)>; 64],
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
}
impl std::str::FromStr for Fen {
    type Err = FenError;

    fn from_str(fen_str: &str) -> Result<Self, Self::Err> {
        if !fen_str.is_ascii() {
            return Err(FenError::NonAscii);
        }

        let mut pieces = [None; 64];
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
                    pieces[squares.next().ok_or(FenError::TooManySquares)? as usize] =
                        Some((PieceKind::Pawn, colour))
                }
                'n' => {
                    pieces[squares.next().ok_or(FenError::TooManySquares)? as usize] =
                        Some((PieceKind::Knight, colour))
                }
                'b' => {
                    pieces[squares.next().ok_or(FenError::TooManySquares)? as usize] =
                        Some((PieceKind::Bishop, colour))
                }
                'r' => {
                    pieces[squares.next().ok_or(FenError::TooManySquares)? as usize] =
                        Some((PieceKind::Rook, colour))
                }
                'q' => {
                    pieces[squares.next().ok_or(FenError::TooManySquares)? as usize] =
                        Some((PieceKind::Queen, colour))
                }
                'k' => {
                    pieces[squares.next().ok_or(FenError::TooManySquares)? as usize] =
                        Some((PieceKind::King, colour))
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
            pieces,
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
        // Pieces
        let mut skip = 0;
        let mut line_length = 0;
        for sq in Square::squares_fen_iter() {
            if let Some((piece, colour)) = self.pieces[sq as usize] {
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
