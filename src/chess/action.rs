//! # Representation, parsing and formatting of chess actions (moves).
//! Contains multiple move representations (internal, UCI and SAN) complete with
//! methods for formatting, converting and parsing such representations.
//!
//! Note that parsing implementations do not check for the legality of parsed moves,
//! only their grammatical correctness. Moves such as "Ke7xb2" will be parsed
//! successfully, even though they are illegal.
//!
//! Checking for legality is deffered to the conversion to the internal move representation
//! by a [`Position`] object.

use thiserror::Error;

use crate::parsing::PartialFromStr;

use super::{
    colour::Colour,
    piece::{Piece, PieceKind, PromotionTarget},
    position::{CheckKind, Position},
    square::{File, FileParseError, Rank, RankParseError, Square, SquareParseError},
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

/// Internal efficient representation of moves
/// with all relevant information stored compactly.
///
/// # Conversion
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
    #[allow(dead_code)]
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
    #[allow(dead_code)]
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

    #[inline(always)]
    pub(crate) const fn promotion_target_type(self) -> Option<PromotionTarget> {
        if self.0 & Self::PROMOTION != 0 {
            Some(unsafe {
                std::mem::transmute::<u8, PromotionTarget>(
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
/// # Parsing
/// Follows a `<from><to>[promotion]` format. Letters for files and piece symbols
/// for promotion targets are case insensitive.
///
/// # Conversion
/// These can be passed to a [`Position`] to convert them into [`Action`],
/// which are then usable for making moves.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct UciMove {
    pub origin: Square,
    pub target: Square,
    pub promoting_to: Option<PromotionTarget>,
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
            promoting_to: value.promotion_target_type(),
        }
    }
}
impl From<&Action> for UciMove {
    fn from(value: &Action) -> Self {
        Self {
            origin: value.origin(),
            target: value.target(),
            promoting_to: value.promotion_target_type(),
        }
    }
}
impl std::fmt::Display for UciMove {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.origin, self.target)?;
        if let Some(kind) = self.promoting_to.map(|p| p.to_piece_kind()) {
            write!(f, "{kind}")?
        }
        Ok(())
    }
}

/// Errors that may arise when parsing UCI moves.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Error)]
pub enum UciParseError {
    #[error("Invalid origin square: {0}")]
    InvalidOriginSquare(SquareParseError),
    #[error("Invalid target square: {0}")]
    InvalidTargetSquare(SquareParseError),
    #[error("A UCI move can only be up to 5 characters long")]
    InputTooLong,
}
impl PartialFromStr for UciMove {
    type Err = UciParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let (origin, s) =
            Square::partial_from_str(s).map_err(|e| UciParseError::InvalidOriginSquare(e))?;
        let (target, s) =
            Square::partial_from_str(s).map_err(|e| UciParseError::InvalidTargetSquare(e))?;
        let (promoting_to, s) = Option::<PromotionTarget>::partial_from_str(s).unwrap();
        Ok((
            Self {
                origin,
                target,
                promoting_to,
            },
            s,
        ))
    }
}

impl std::str::FromStr for UciMove {
    type Err = UciParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(result, rest)| {
            if rest.is_empty() {
                Ok(result)
            } else {
                Err(UciParseError::InputTooLong)
            }
        })
    }
}

/// Different types of moves that can be encoded using Standard Algebraic Notation,
/// without check/checkmate information.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum SanMoveKind {
    PieceMove {
        moving_piece: PieceKind,
        origin_file: Option<File>,
        origin_rank: Option<Rank>,
        is_capture: bool,
        target: Square,
    },
    PawnPush {
        target: Square,
        promoting_to: Option<PromotionTarget>,
    },
    PawnCapture {
        origin_file: File,
        target: Square,
        promoting_to: Option<PromotionTarget>,
    },
    KingSideCastle,
    QueenSideCastle,
}
impl std::fmt::Display for SanMoveKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::PieceMove {
                moving_piece,
                origin_file,
                origin_rank,
                is_capture,
                target,
            } => {
                if moving_piece != PieceKind::Pawn {
                    write!(f, "{moving_piece}")?;
                }
                if let Some(file) = origin_file {
                    write!(f, "{file}")?
                }
                if let Some(rank) = origin_rank {
                    write!(f, "{rank}")?
                }
                if is_capture {
                    write!(f, "x")?
                }
                write!(f, "{target}")?;
                Ok(())
            }
            Self::PawnPush {
                target,
                promoting_to,
            } => {
                write!(f, "{target}")?;
                if let Some(p) = promoting_to {
                    write!(f, "={p}")?
                }
                Ok(())
            }
            Self::PawnCapture {
                origin_file,
                target,
                promoting_to,
            } => {
                write!(f, "{origin_file}")?;
                write!(f, "x")?;
                write!(f, "{target}")?;
                if let Some(p) = promoting_to {
                    write!(f, "={p}")?
                }
                Ok(())
            }
            Self::KingSideCastle => write!(f, "O-O"),
            Self::QueenSideCastle => write!(f, "O-O-O"),
        }
    }
}

/// Standard Algebraic Notation (SAN) encoded move, mainly used in Portable Game Notation
/// and/or for human-readability (in UCI debug mode for example).
///
/// # Parsing
/// The SAN notation used follows the PGN standard:
/// - O-O or O-O-O for king and queenside castles respectively
/// - Piece symbol (can be ommited for pawns)
/// - Disambiguation of source square if needed
/// - Optional capture marker
/// - Target square
/// - `=<Piece symbol>` for promotions
/// - Optional checkmate (`#`) or check (`+`) marker
///
/// Parsing is as fault tolerant as possible:
/// - Check(mate) markers can be ommited
/// - Indicating piece symbol for pawns is accepted
/// - Case insensitive (`kD4` for example is accepted)
///
/// # Conversion
/// SAN encoded moves include/lack context that is ommitted/required by other move representations,
/// and therefore cannot be directly converted to/obtained from [`Action`] or [`UciMove`] types.
/// Refer to [`Position::encode_san`] and [`Position::decode_san`] for conversions.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct SanMove {
    pub move_kind: SanMoveKind,
    pub check: Option<CheckKind>,
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
        write!(f, "{}", self.move_kind)?;
        match self.check {
            Some(CheckKind::CheckMate) => write!(f, "#")?,
            Some(_) => write!(f, "+")?,
            None => (),
        }
        Ok(())
    }
}

/// Errors that may arise when parsing SAN moves.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Error)]
pub enum SanParseError {
    #[error("Invalid origin file: {0}")]
    InvalidOriginFile(#[from] FileParseError),
    #[error("Invalid origin rank: {0}")]
    InvalidOriginRank(#[from] RankParseError),
    #[error("Invalid target square: {0}")]
    InvalidTargetSquare(#[from] SquareParseError),
    #[error("Cannot promote {0}")]
    PromotingNonPawnPiece(PieceKind),
    #[error("Some part of the input was left after parsing a SAN move")]
    InputTooLong,
}
impl PartialFromStr for SanMove {
    type Err = SanParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let (move_kind, s) = if s.len() >= "O-O-O".len() && &s[0.."O-O-O".len()] == "O-O-O" {
            (SanMoveKind::QueenSideCastle, &s["O-O-O".len()..])
        } else if s.len() >= "O-O".len() && &s[0.."O-O".len()] == "O-O" {
            (SanMoveKind::KingSideCastle, &s["O-O".len()..])
        } else {
            let (moving_piece, s) = Option::<PieceKind>::partial_from_str(s)
                .map(|(p, s)| (p.unwrap_or(PieceKind::Pawn), s))
                .unwrap();
            let (origin_file, s) = Result::<File, FileParseError>::partial_from_str(s).unwrap();
            let (origin_rank, s) = Result::<Rank, RankParseError>::partial_from_str(s).unwrap();
            let is_capture = s.chars().next() == Some('x');
            let s = if is_capture { &s[1..] } else { s };
            let ((target, s), origin_file, origin_rank) = match Square::partial_from_str(s) {
                Ok(v) => (v, origin_file.ok(), origin_rank.ok()),
                Err(e) => {
                    // The origin rank and file would define the target square in
                    // this scenario.
                    if is_capture {
                        Err(SanParseError::InvalidTargetSquare(e))?
                    }
                    let file = origin_file.map_err(|e| SanParseError::InvalidOriginFile(e))?;
                    let rank = origin_rank.map_err(|e| SanParseError::InvalidOriginRank(e))?;
                    ((Square::new(file, rank), s), None, None)
                }
            };

            let (promotion, s) = if s.chars().next() == Some('=') {
                let after_eq = &s[1..];
                match Option::<PromotionTarget>::partial_from_str(after_eq) {
                    Ok(v) => v,
                    Err(_) => (None, s),
                }
            } else {
                Option::<PromotionTarget>::partial_from_str(s).unwrap()
            };

            if moving_piece != PieceKind::Pawn && promotion.is_some() {
                Err(SanParseError::PromotingNonPawnPiece(moving_piece))?
            }

            let mv = if moving_piece == PieceKind::Pawn {
                if is_capture {
                    SanMoveKind::PawnCapture {
                        origin_file: origin_file.unwrap(),
                        target,
                        promoting_to: promotion,
                    }
                } else {
                    SanMoveKind::PawnPush {
                        target,
                        promoting_to: promotion,
                    }
                }
            } else {
                SanMoveKind::PieceMove {
                    moving_piece,
                    origin_file,
                    origin_rank,
                    is_capture,
                    target,
                }
            };
            (mv, s)
        };

        let check = match s.chars().next() {
            Some('+') => Some(CheckKind::Check),
            Some('#') => Some(CheckKind::CheckMate),
            _ => None,
        };
        let san_move = SanMove { move_kind, check };

        Ok((san_move, if check.is_some() { &s[1..] } else { s }))
    }
}
impl std::str::FromStr for SanMove {
    type Err = SanParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(result, rest)| {
            if rest.is_empty() {
                Ok(result)
            } else {
                Err(SanParseError::InputTooLong)
            }
        })
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
                promoting_to: Some(PromotionTarget::Bishop)
            })
        );
    }

    #[test]
    fn uci_parse_invalid_origin() {
        assert_eq!(
            "l3e5".parse::<UciMove>(),
            Err(UciParseError::InvalidOriginSquare(
                SquareParseError::InvalidFile(FileParseError::InvalidFileSymbol('l'))
            ))
        );
    }

    #[test]
    fn uci_parse_invalid_target() {
        assert_eq!(
            "e3e9".parse::<UciMove>(),
            Err(UciParseError::InvalidTargetSquare(
                SquareParseError::InvalidRank(RankParseError::InvalidRankSymbol('9'))
            ))
        );
    }

    #[test]
    fn uci_parse_invalid_promotion() {
        assert_eq!("e4e5p".parse::<UciMove>(), Err(UciParseError::InputTooLong));
        assert_eq!("e4e5l".parse::<UciMove>(), Err(UciParseError::InputTooLong));
    }

    #[test]
    fn uci_parse_too_small() {
        assert_eq!(
            "e4e".parse::<UciMove>(),
            Err(UciParseError::InvalidTargetSquare(
                SquareParseError::InvalidRank(RankParseError::EmptyInput)
            ))
        );
    }

    #[test]
    fn uci_parse_leftovers() {
        assert_eq!(
            "e4e5bk".parse::<UciMove>(),
            Err(UciParseError::InputTooLong)
        );
    }

    #[test]
    fn san_castling() {
        assert_eq!(
            "O-O".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::KingSideCastle)
        );
        assert_eq!(
            "O-O-O".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::QueenSideCastle)
        );
    }

    #[test]
    fn san_pawn_push() {
        assert_eq!(
            "e4".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PawnPush {
                target: Square::E4,
                promoting_to: None
            })
        );
    }

    #[test]
    fn san_pawn_push_promotion() {
        assert_eq!(
            "e8=b".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PawnPush {
                target: Square::E8,
                promoting_to: Some(PromotionTarget::Bishop)
            })
        );
    }

    #[test]
    fn san_pawn_push_invalid_promotion() {
        assert_eq!("e4=p".parse::<SanMove>(), Err(SanParseError::InputTooLong));
    }

    #[test]
    fn san_pawn_push_leftovers() {
        assert_eq!("f7=bl".parse::<SanMove>(), Err(SanParseError::InputTooLong));
    }

    #[test]
    fn san_pawn_capture() {
        assert_eq!(
            "exd6".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PawnCapture {
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
            Err(SanParseError::InvalidOriginFile(
                FileParseError::InvalidFileSymbol('l')
            ))
        )
    }

    #[test]
    fn san_pawn_capture_invalid_target() {
        assert_eq!(
            "exle".parse::<SanMove>(),
            Err(SanParseError::InvalidTargetSquare(
                SquareParseError::InvalidFile(FileParseError::InvalidFileSymbol('l'))
            ))
        )
    }

    #[test]
    fn san_pawn_capture_promotion() {
        assert_eq!(
            "exf7=n".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PawnCapture {
                origin_file: File::E,
                target: Square::F7,
                promoting_to: Some(PromotionTarget::Knight)
            })
        )
    }

    #[test]
    fn san_pawn_capture_invalid_promotion() {
        assert_eq!(
            "exf7=p".parse::<SanMove>(),
            Err(SanParseError::InputTooLong)
        );
    }

    #[test]
    fn san_pawn_capture_unconsumed_chars() {
        assert_eq!(
            "exf7=bl".parse::<SanMove>(),
            Err(SanParseError::InputTooLong)
        );
    }

    #[test]
    fn san_piece_move_unambiguous() {
        assert_eq!(
            "Nf7".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PieceMove {
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
            "bec7".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PieceMove {
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
            "Q7b7".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PieceMove {
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
            "Re7b7".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PieceMove {
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
            "Rxb7".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PieceMove {
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
            "bexc7".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PieceMove {
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
            "Q7xb7".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PieceMove {
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
            "Re7xb7".parse::<SanMove>().map(|m| m.move_kind),
            Ok(SanMoveKind::PieceMove {
                moving_piece: PieceKind::Rook,
                origin_rank: Some(Rank::Seven),
                origin_file: Some(File::E),
                is_capture: true,
                target: Square::B7
            })
        );
    }

    #[test]
    fn san_non_pawn_promotion() {
        assert_eq!(
            "Re7=Q".parse::<SanMove>(),
            Err(SanParseError::PromotingNonPawnPiece(PieceKind::Rook))
        )
    }

    #[test]
    fn san_piece_move_unconsumated_chars() {
        assert_eq!("Re7l".parse::<SanMove>(), Err(SanParseError::InputTooLong));
        assert_eq!("Rbe7l".parse::<SanMove>(), Err(SanParseError::InputTooLong));
        assert_eq!(
            "Rb5e7l".parse::<SanMove>(),
            Err(SanParseError::InputTooLong)
        );
        assert_eq!("Rxe7l".parse::<SanMove>(), Err(SanParseError::InputTooLong));
        assert_eq!(
            "Rbxe7l".parse::<SanMove>(),
            Err(SanParseError::InputTooLong)
        );
        assert_eq!(
            "Rb5xe7l".parse::<SanMove>(),
            Err(SanParseError::InputTooLong)
        );
    }

    #[test]
    fn san_check() {
        assert_eq!(
            "RxB7+".parse::<SanMove>().unwrap().check,
            Some(CheckKind::Check)
        );
    }
    #[test]
    fn san_checkmate() {
        assert_eq!(
            "e8=Q#".parse::<SanMove>().unwrap().check,
            Some(CheckKind::CheckMate)
        );
    }
}
