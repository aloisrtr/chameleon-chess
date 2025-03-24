//! # Representation, parsing and formatting of chess actions (moves).
//! Contains multiple move representations (internal, UCI and SAN) complete with
//! methods for formatting, converting and parsing such representations.

use thiserror::Error;

use super::{
    colour::Colour,
    piece::{Piece, PieceKind},
    position::Position,
    square::{File, Rank, Square},
};

/// Generic trait for types that can act as chess moves. This trait includes conversions
/// from and to the internal [`Action`] representation using a [`Position`]
/// object for added context, and can be used as input to [`Position::make`](crate::chess::position::Position::make).
pub trait ChessMove: Sized {
    /// Converts an internal representation of [`Actions`](self::Action) to this type.
    ///
    /// Returns `None` if the move is illegal in the given [`Position`].
    fn from_action(action: Action, position: &Position) -> Option<Self>;

    /// Converts this type to the internal representation of [`Actions`](self::Action).
    ///
    /// Returns `None` if this move is illegal in the given [`Position`].
    fn to_action(&self, position: &Position) -> Option<Action>;
}

/// Internal efficient representation of moves using a from-to \<promotion\> approach,
/// with all relevant information stored compactly.
///
/// Most methods of this type are only visible at the crate level, as it provides
/// poor and low-level API for modifying, parsing or accessing move information.
/// Users should instead opt to use either [`UciMove`] or [`SanMove`].
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Action(u16);
impl Action {
    const ORIGIN_MASK: u16 = 0x003F;
    const TARGET_MASK: u16 = Self::ORIGIN_MASK << 6;
    const PROMOTION: u16 = 1 << 15;
    const CAPTURE: u16 = 1 << 14;
    const SPECIAL_0: u16 = 1 << 12;
    const SPECIAL_1: u16 = 1 << 13;
    const PROMOTING_PIECE: u16 = Self::SPECIAL_0 | Self::SPECIAL_1;

    /// Creates a new quiet move.
    #[inline(always)]
    pub(crate) const fn new_quiet(origin: Square, target: Square) -> Self {
        Self(origin as u16 | (target as u16) << 6)
    }

    /// Creates a new capture.
    #[inline(always)]
    pub(crate) const fn new_capture(origin: Square, target: Square) -> Self {
        Self(origin as u16 | (target as u16) << 6 | Self::CAPTURE)
    }

    /// Creates a new double push.
    #[inline(always)]
    pub(crate) const fn new_double_push(origin: Square, target: Square) -> Self {
        Self(origin as u16 | (target as u16) << 6 | Self::SPECIAL_0)
    }

    /// Returns a new promoting move.
    pub(crate) const fn new_promotion(
        origin: Square,
        target: Square,
        promoting_to: PieceKind,
    ) -> Self {
        Self(
            origin as u16
                | (target as u16) << 6
                | Self::PROMOTION
                | (promoting_to as u16 - PieceKind::Knight as u16) << 12,
        )
    }

    /// Creates a set of promotions from a pawn push.
    #[inline(always)]
    pub(crate) const fn new_promotions(origin: Square, target: Square) -> [Self; 4] {
        let general_move = origin as u16 | (target as u16) << 6 | Self::PROMOTION;
        [
            Self(general_move),
            Self(general_move | (1 << 12)),
            Self(general_move | (2 << 12)),
            Self(general_move | (3 << 12)),
        ]
    }

    /// Returns a new promoting move with capture.
    pub(crate) const fn new_promotion_capture(
        origin: Square,
        target: Square,
        promoting_to: PieceKind,
    ) -> Self {
        Self(
            origin as u16
                | (target as u16) << 6
                | Self::PROMOTION
                | Self::CAPTURE
                | (promoting_to as u16 - PieceKind::Knight as u16) << 12,
        )
    }

    /// Creates a set of promotions from a pawn capture.
    #[inline(always)]
    pub(crate) const fn new_promotion_captures(origin: Square, target: Square) -> [Self; 4] {
        let general_move = origin as u16 | (target as u16) << 6 | Self::PROMOTION | Self::CAPTURE;
        [
            Self(general_move),
            Self(general_move | (1 << 12)),
            Self(general_move | (2 << 12)),
            Self(general_move | (3 << 12)),
        ]
    }

    /// Creates an en passant capture.
    #[inline(always)]
    pub(crate) const fn new_en_passant(origin: Square, target: Square) -> Self {
        Self(origin as u16 | (target as u16) << 6 | Self::CAPTURE | Self::SPECIAL_0)
    }

    /// Creates an en passant queenside castle move.
    #[inline(always)]
    pub(crate) const fn new_queenside_castle(side: Colour) -> Self {
        if side.is_black() {
            Self(Square::E8 as u16 | (Square::C8 as u16) << 6 | Self::SPECIAL_0 | Self::SPECIAL_1)
        } else {
            Self(Square::E1 as u16 | (Square::C1 as u16) << 6 | Self::SPECIAL_0 | Self::SPECIAL_1)
        }
    }

    /// Creates an en passant kingside castle move.
    #[inline(always)]
    pub(crate) const fn new_kingside_castle(side: Colour) -> Self {
        if side.is_black() {
            Self(Square::E8 as u16 | (Square::G8 as u16) << 6 | Self::SPECIAL_1)
        } else {
            Self(Square::E1 as u16 | (Square::G1 as u16) << 6 | Self::SPECIAL_1)
        }
    }

    /// Returns the square the move originates from.
    #[inline(always)]
    pub const fn origin(self) -> Square {
        unsafe { Square::from_index_unchecked((self.0 & Self::ORIGIN_MASK) as u8) }
    }
    /// Returns the square the move targets.
    #[inline(always)]
    pub const fn target(self) -> Square {
        unsafe { Square::from_index_unchecked(((self.0 & Self::TARGET_MASK) >> 6) as u8) }
    }

    /// Checks if this move is a capture.
    #[inline(always)]
    pub const fn is_capture(self) -> bool {
        self.0 & Self::CAPTURE != 0
    }

    /// Checks if this move is a promotion, and returns the promotion target if so.
    #[inline(always)]
    pub const fn promotion_target(self) -> Option<PieceKind> {
        if self.0 & Self::PROMOTION != 0 {
            Some(unsafe {
                std::mem::transmute::<u8, PieceKind>(
                    ((self.0 & Self::PROMOTING_PIECE) >> 12) as u8 + 1,
                )
            })
        } else {
            None
        }
    }

    /// Checks if this move encodes a queenside castle.
    #[inline(always)]
    pub const fn is_queenside_castle(self) -> bool {
        self.promotion_target().is_none()
            && !self.is_capture()
            && self.special_1_is_set()
            && self.special_0_is_set()
    }

    /// Checks if this move encodes a kingside castle.
    #[inline(always)]
    pub const fn is_kingside_castle(self) -> bool {
        self.promotion_target().is_none()
            && !self.is_capture()
            && self.special_1_is_set()
            && !self.special_0_is_set()
    }

    /// Checks if the SPECIAL_0 bit is set.
    #[inline(always)]
    pub(crate) const fn special_0_is_set(self) -> bool {
        self.0 & Self::SPECIAL_0 != 0
    }
    /// Checks if the SPECIAL_1 bit is set.
    #[inline(always)]
    pub(crate) const fn special_1_is_set(self) -> bool {
        self.0 & Self::SPECIAL_1 != 0
    }
}
impl std::fmt::Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.origin(),
            self.target(),
            if let Some(piece_kind) = self.promotion_target() {
                piece_kind.to_string()
            } else {
                String::new()
            }
        )
    }
}
impl ChessMove for Action {
    fn from_action(action: Action, position: &Position) -> Option<Self> {
        if position.is_legal(action) {
            Some(action)
        } else {
            None
        }
    }

    fn to_action(&self, position: &Position) -> Option<Action> {
        if position.is_legal(*self) {
            Some(*self)
        } else {
            None
        }
    }
}

/// Pure coordinate notation move, mainly used for parsing UCI commands.
///
/// These can be passed to a [`Position`] to convert them into [`Action`],
/// which are then usable for making moves.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct UciMove {
    pub origin: Square,
    pub target: Square,
    pub promoting_to: Option<PieceKind>,
}
impl ChessMove for UciMove {
    fn from_action(action: Action, position: &Position) -> Option<Self> {
        position.decode_uci(action)
    }
    fn to_action(&self, position: &Position) -> Option<Action> {
        position.encode_uci(*self)
    }
}
impl From<Action> for UciMove {
    fn from(value: Action) -> Self {
        Self {
            origin: value.origin(),
            target: value.target(),
            promoting_to: value.promotion_target(),
        }
    }
}
impl From<&Action> for UciMove {
    fn from(value: &Action) -> Self {
        Self {
            origin: value.origin(),
            target: value.target(),
            promoting_to: value.promotion_target(),
        }
    }
}
impl std::fmt::Display for UciMove {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.origin, self.target)?;
        if let Some(kind) = self.promoting_to {
            write!(f, "{kind}")?
        }
        Ok(())
    }
}

/// Errors that may arise when parsing UCI moves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Error)]
pub enum UciParseError {
    #[error("Invalid origin square")]
    InvalidOriginSquare,
    #[error("Invalid target square")]
    InvalidTargetSquare,
    #[error("Cannot promote to {0:?}")]
    InvalidPromotion(Option<PieceKind>),
    #[error("UCI moves are at least 4 characters, got {0}")]
    TooLittleChars(usize),
    #[error("UCI moves are at most 5 characters, got {0}")]
    TooManyChars(usize),
}

impl std::str::FromStr for UciMove {
    type Err = UciParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() < 4 {
            return Err(UciParseError::TooLittleChars(s.len()));
        } else if s.len() > 5 {
            return Err(UciParseError::TooManyChars(s.len()));
        }

        let from = s[0..2]
            .parse()
            .map_err(|_| UciParseError::InvalidOriginSquare)?;
        let to = s[2..4]
            .parse()
            .map_err(|_| UciParseError::InvalidTargetSquare)?;
        let promoting_to = if s.len() == 5 {
            if let Ok(piece) = s[4..5].parse::<Piece>() {
                if piece.kind.is_valid_promotion_target() {
                    Some(piece.kind)
                } else {
                    Err(UciParseError::InvalidPromotion(Some(piece.kind)))?
                }
            } else {
                Err(UciParseError::InvalidPromotion(None))?
            }
        } else {
            None
        };

        Ok(Self {
            origin: from,
            target: to,
            promoting_to,
        })
    }
}

/// Standard Algebraic Notation (SAN) encoded move, mainly used in Portable Game Notation
/// and/or for human-readability (in UCI debug mode for example).
///
/// SAN encoded moves include/lack context that is ommitted/required by other move representations,
/// and therefore cannot be directly converted to/obtained from [`Action`] or [`UciMove`] types.
/// Refer to [`Position::encode_san`] and [`Position::decode_san`] for conversions.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum SanMove {
    PawnPush {
        target: Square,
        promoting_to: Option<PieceKind>,
    },
    PawnCapture {
        origin_file: File,
        target: Square,
        promoting_to: Option<PieceKind>,
    },
    PieceMove {
        moving_piece: PieceKind,
        origin_file: Option<File>,
        origin_rank: Option<Rank>,
        is_capture: bool,
        target: Square,
    },
    KingSideCastle,
    QueenSideCastle,
}
impl ChessMove for SanMove {
    fn from_action(action: Action, position: &Position) -> Option<Self> {
        position.decode_san(action)
    }

    fn to_action(&self, position: &Position) -> Option<Action> {
        position.encode_san(*self)
    }
}
impl std::fmt::Display for SanMove {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::PawnPush {
                target,
                promoting_to,
            } => {
                write!(f, "{target}")?;
                if let Some(kind) = promoting_to {
                    write!(f, "{kind}")?
                }
                Ok(())
            }
            Self::PawnCapture {
                origin_file,
                target,
                promoting_to,
            } => {
                write!(f, "{origin_file}x{target}")?;
                if let Some(kind) = promoting_to {
                    write!(f, "{kind}")?
                }
                Ok(())
            }
            Self::PieceMove {
                moving_piece,
                origin_file,
                origin_rank,
                is_capture,
                target,
            } => {
                write!(f, "{}", moving_piece.to_string().to_uppercase())?;
                match (origin_file, origin_rank) {
                    (None, None) => (),
                    (Some(file), None) => write!(f, "{file}")?,
                    (None, Some(rank)) => write!(f, "{rank}")?,
                    (Some(file), Some(rank)) => write!(f, "{file}{rank}")?,
                };
                if is_capture {
                    write!(f, "x")?
                }
                write!(f, "{target}")
            }
            Self::KingSideCastle => write!(f, "O-O"),
            Self::QueenSideCastle => write!(f, "O-O-O"),
        }
    }
}

/// Errors that may arise when parsing SAN moves.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Error)]
pub enum SanParseError {
    #[error("Missing target square")]
    MissingTargetSquare,
    #[error("Invalid target square")]
    InvalidTargetSquare,
    #[error("First character is invalid for SAN moves")]
    InvalidFirstCharacter,
    #[error("Cannot promote to {0:?}")]
    InvalidPromotion(Option<PieceKind>),
    #[error("{0} characters left unconsumed after successful SAN parse")]
    UnconsumedChars(usize),
    #[error("SAN moves are at least 2 characters, got {0}")]
    TooLittleChars(usize),
    #[error("SAN moves are at most 6 characters, got {0}")]
    TooManyChars(usize),
}

impl std::str::FromStr for SanMove {
    type Err = SanParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() < 2 {
            return Err(SanParseError::TooLittleChars(s.len()));
        } else if s.len() > 6 {
            return Err(SanParseError::TooManyChars(s.len()));
        }

        if let Ok(piece) = s[0..1].parse::<Piece>() {
            // Piece move parsing
            let (mut file, mut rank, mut next_index) = if let Ok(file) = s[1..2].parse::<File>() {
                if let Ok(rank) = s[2..3].parse::<Rank>() {
                    (Some(file), Some(rank), 3)
                } else {
                    (Some(file), None, 2)
                }
            } else if let Ok(rank) = s[1..2].parse::<Rank>() {
                (None, Some(rank), 2)
            } else {
                (None, None, 1)
            };

            let (target, is_capture) = if s.len() >= next_index + 3 {
                if &s[next_index..next_index + 1] != "x" {
                    return Err(SanParseError::UnconsumedChars(1));
                }
                let target = s[next_index + 1..next_index + 3]
                    .parse::<Square>()
                    .map_err(|_| SanParseError::InvalidTargetSquare)?;
                next_index += 3;
                (target, true)
            } else if s.len() >= next_index + 2 {
                let target = s[next_index..next_index + 2]
                    .parse::<Square>()
                    .map_err(|_| SanParseError::InvalidTargetSquare)?;
                next_index += 2;
                (target, false)
            } else {
                let target = Square::new(
                    file.ok_or(SanParseError::InvalidTargetSquare)?,
                    rank.ok_or(SanParseError::InvalidTargetSquare)?,
                );
                file = None;
                rank = None;
                (target, false)
            };

            if s.len() > next_index {
                return Err(SanParseError::UnconsumedChars(s.len() - next_index));
            }

            Ok(Self::PieceMove {
                moving_piece: piece.kind,
                origin_file: file,
                origin_rank: rank,
                is_capture,
                target,
            })
        } else if let Ok(file) = s[0..1].parse::<File>() {
            // Pawn move parsing
            if let Ok(rank) = s[1..2].parse::<Rank>() {
                let promoting_to = if s.len() == 3 {
                    let promotion = s[2..3]
                        .parse::<Piece>()
                        .map_err(|_| SanParseError::InvalidPromotion(None))?
                        .kind;
                    if !promotion.is_valid_promotion_target() {
                        return Err(SanParseError::InvalidPromotion(Some(promotion)));
                    }
                    Some(promotion)
                } else if s.len() > 3 {
                    return Err(SanParseError::UnconsumedChars(s.len() - 3));
                } else {
                    None
                };

                Ok(Self::PawnPush {
                    target: Square::new(file, rank),
                    promoting_to,
                })
            } else if &s[1..2] == "x" {
                // Pawn capture
                if s.len() < 4 {
                    // We can't have enough characters to parse the target square.
                    return Err(SanParseError::MissingTargetSquare);
                }
                let target = s[2..4]
                    .parse::<Square>()
                    .map_err(|_| SanParseError::InvalidTargetSquare)?;
                let promoting_to = if s.len() == 5 {
                    let promotion = s[4..5]
                        .parse::<Piece>()
                        .map_err(|_| SanParseError::InvalidPromotion(None))?
                        .kind;

                    if !promotion.is_valid_promotion_target() {
                        return Err(SanParseError::InvalidPromotion(Some(promotion)));
                    }
                    Some(promotion)
                } else if s.len() > 5 {
                    return Err(SanParseError::UnconsumedChars(s.len() - 5));
                } else {
                    None
                };

                Ok(Self::PawnCapture {
                    origin_file: file,
                    target,
                    promoting_to,
                })
            } else {
                // Invalid pawn move or capture
                Err(SanParseError::MissingTargetSquare)
            }
        } else if s == "O-O" {
            Ok(Self::KingSideCastle)
        } else if s == "O-O-O" {
            Ok(Self::QueenSideCastle)
        } else {
            // Invalid first character, we cannot detect what type of move this
            // was supposed to encode.
            Err(SanParseError::InvalidFirstCharacter)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uci_parse() {
        assert_eq!(
            "e4e5".parse(),
            Ok(UciMove {
                origin: Square::E4,
                target: Square::E5,
                promoting_to: None
            })
        );
    }

    #[test]
    fn uci_parse_promotion() {
        assert_eq!(
            "e4e5b".parse(),
            Ok(UciMove {
                origin: Square::E4,
                target: Square::E5,
                promoting_to: Some(PieceKind::Bishop)
            })
        );
    }

    #[test]
    fn uci_parse_invalid_origin() {
        assert_eq!(
            "l3e5".parse::<UciMove>(),
            Err(UciParseError::InvalidOriginSquare)
        );
    }

    #[test]
    fn uci_parse_invalid_target() {
        assert_eq!(
            "e3i6".parse::<UciMove>(),
            Err(UciParseError::InvalidTargetSquare)
        );
    }

    #[test]
    fn uci_parse_invalid_promotion() {
        assert_eq!(
            "e4e5p".parse::<UciMove>(),
            Err(UciParseError::InvalidPromotion(Some(PieceKind::Pawn)))
        );
        assert_eq!(
            "e4e5l".parse::<UciMove>(),
            Err(UciParseError::InvalidPromotion(None))
        );
    }

    #[test]
    fn uci_parse_too_small() {
        assert_eq!(
            "e4e".parse::<UciMove>(),
            Err(UciParseError::TooLittleChars(3))
        );
    }

    #[test]
    fn uci_parse_too_long() {
        assert_eq!(
            "e4e5bk".parse::<UciMove>(),
            Err(UciParseError::TooManyChars(6))
        );
    }

    #[test]
    fn san_castling() {
        assert_eq!("O-O".parse(), Ok(SanMove::KingSideCastle));
        assert_eq!("O-O-O".parse(), Ok(SanMove::QueenSideCastle));
    }

    #[test]
    fn san_pawn_push() {
        assert_eq!(
            "e4".parse(),
            Ok(SanMove::PawnPush {
                target: Square::E4,
                promoting_to: None
            })
        );
    }

    #[test]
    fn san_pawn_push_promotion() {
        assert_eq!(
            "e8b".parse(),
            Ok(SanMove::PawnPush {
                target: Square::E8,
                promoting_to: Some(PieceKind::Bishop)
            })
        );
    }

    #[test]
    fn san_pawn_push_invalid_promotion() {
        assert_eq!(
            "e4p".parse::<SanMove>(),
            Err(SanParseError::InvalidPromotion(Some(PieceKind::Pawn)))
        );
        assert_eq!(
            "e4l".parse::<SanMove>(),
            Err(SanParseError::InvalidPromotion(None))
        );
    }

    #[test]
    fn san_pawn_push_unconsumed_chars() {
        assert_eq!(
            "f7bl".parse::<SanMove>(),
            Err(SanParseError::UnconsumedChars(1))
        );
    }

    #[test]
    fn san_pawn_capture() {
        assert_eq!(
            "exd6".parse(),
            Ok(SanMove::PawnCapture {
                origin_file: File::E,
                target: Square::D6,
                promoting_to: None
            })
        )
    }

    #[test]
    fn san_pawn_capture_invalid_file() {
        assert_eq!(
            "lxe4".parse::<SanMove>(),
            Err(SanParseError::InvalidFirstCharacter)
        )
    }

    #[test]
    fn san_pawn_capture_invalid_target() {
        assert_eq!(
            "exle".parse::<SanMove>(),
            Err(SanParseError::InvalidTargetSquare)
        )
    }

    #[test]
    fn san_pawn_capture_promotion() {
        assert_eq!(
            "exf7n".parse::<SanMove>(),
            Ok(SanMove::PawnCapture {
                origin_file: File::E,
                target: Square::F7,
                promoting_to: Some(PieceKind::Knight)
            })
        )
    }

    #[test]
    fn san_pawn_capture_invalid_promotion() {
        assert_eq!(
            "exf7p".parse::<SanMove>(),
            Err(SanParseError::InvalidPromotion(Some(PieceKind::Pawn)))
        );
        assert_eq!(
            "exf7l".parse::<SanMove>(),
            Err(SanParseError::InvalidPromotion(None))
        );
    }

    #[test]
    fn san_pawn_capture_unconsumed_chars() {
        assert_eq!(
            "exf7bl".parse::<SanMove>(),
            Err(SanParseError::UnconsumedChars(1))
        );
    }

    #[test]
    fn san_piece_move_unambiguous() {
        assert_eq!(
            "Nf7".parse::<SanMove>(),
            Ok(SanMove::PieceMove {
                moving_piece: PieceKind::Knight,
                origin_file: None,
                origin_rank: None,
                is_capture: false,
                target: Square::F7
            })
        );
    }

    #[test]
    fn san_piece_move_file_ambiguity() {
        assert_eq!(
            "bec7".parse::<SanMove>(),
            Ok(SanMove::PieceMove {
                moving_piece: PieceKind::Bishop,
                origin_file: Some(File::E),
                origin_rank: None,
                is_capture: false,
                target: Square::C7
            })
        );
    }

    #[test]
    fn san_piece_move_rank_ambiguity() {
        assert_eq!(
            "Q7b7".parse::<SanMove>(),
            Ok(SanMove::PieceMove {
                moving_piece: PieceKind::Queen,
                origin_rank: Some(Rank::Seven),
                origin_file: None,
                is_capture: false,
                target: Square::B7
            })
        );
    }

    #[test]
    fn san_piece_move_rank_and_file_ambiguity() {
        assert_eq!(
            "Re7b7".parse::<SanMove>(),
            Ok(SanMove::PieceMove {
                moving_piece: PieceKind::Rook,
                origin_rank: Some(Rank::Seven),
                origin_file: Some(File::E),
                is_capture: false,
                target: Square::B7
            })
        );
    }

    #[test]
    fn san_piece_capture() {
        assert_eq!(
            "Rxb7".parse::<SanMove>(),
            Ok(SanMove::PieceMove {
                moving_piece: PieceKind::Rook,
                origin_rank: None,
                origin_file: None,
                is_capture: true,
                target: Square::B7
            })
        );
    }

    #[test]
    fn san_piece_capture_file_ambiguity() {
        assert_eq!(
            "bexc7".parse::<SanMove>(),
            Ok(SanMove::PieceMove {
                moving_piece: PieceKind::Bishop,
                origin_file: Some(File::E),
                origin_rank: None,
                is_capture: true,
                target: Square::C7
            })
        );
    }

    #[test]
    fn san_piece_capture_rank_ambiguity() {
        assert_eq!(
            "Q7xb7".parse::<SanMove>(),
            Ok(SanMove::PieceMove {
                moving_piece: PieceKind::Queen,
                origin_rank: Some(Rank::Seven),
                origin_file: None,
                is_capture: true,
                target: Square::B7
            })
        );
    }

    #[test]
    fn san_piece_capture_rank_and_file_ambiguity() {
        assert_eq!(
            "Re7xb7".parse::<SanMove>(),
            Ok(SanMove::PieceMove {
                moving_piece: PieceKind::Rook,
                origin_rank: Some(Rank::Seven),
                origin_file: Some(File::E),
                is_capture: true,
                target: Square::B7
            })
        );
    }

    #[test]
    fn san_piece_move_unconsumated_chars() {
        assert_eq!(
            "Re7l".parse::<SanMove>(),
            Err(SanParseError::UnconsumedChars(1))
        );
        assert_eq!(
            "Rbe7l".parse::<SanMove>(),
            Err(SanParseError::UnconsumedChars(1))
        );
        assert_eq!(
            "Rb5e7l".parse::<SanMove>(),
            Err(SanParseError::UnconsumedChars(1))
        );
        assert_eq!(
            "Rxe7l".parse::<SanMove>(),
            Err(SanParseError::UnconsumedChars(1))
        );
        assert_eq!(
            "Rbxe7l".parse::<SanMove>(),
            Err(SanParseError::UnconsumedChars(1))
        );
        assert_eq!(
            "Rb5xe7l".parse::<SanMove>(),
            Err(SanParseError::TooManyChars(7))
        );
    }

    #[test]
    fn san_invalid_first_char() {
        assert_eq!(
            "oe7l".parse::<SanMove>(),
            Err(SanParseError::InvalidFirstCharacter)
        );
    }
}
