//! # Representation, parsing and formatting of chess actions (moves).
//! Contains multiple move representations (internal, UCI and SAN) complete with
//! methods for formatting, converting and parsing such representations.

use super::{
    colour::Colour,
    piece::PieceKind,
    position::Position,
    square::{File, Rank, Square},
};

/// Generic trait for types that can act as chess moves. This trait includes conversions
/// from and to the internal [`Action`] representation using a [`Position`](crate::chess::position::Position)
/// object for added context, and can be used as input to [`Position::make`](crate::chess::position::Position::make).
pub trait ChessMove: Sized {
    /// Converts an internal representation of [`Actions`](self::Action) to this type.
    ///
    /// Returns `None` if the move is illegal in the given [`Position`](crate::chess::position::Position).
    fn from_action(action: Action, position: &Position) -> Option<Self>;

    /// Converts this type to the internal representation of [`Actions`](self::Action).
    ///
    /// Returns `None` if this move is illegal in the given [`Position`](crate::chess::position::Position).
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
/// These can be passed to a [`Position`](crate::game::position::Position) to convert them into [`Action`],
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
impl std::str::FromStr for UciMove {
    // TODO: Parsing errors
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let from = s[0..2].parse().unwrap();
        let to = s[2..4].parse().unwrap();
        let promoting_to = if s.len() == 5 {
            match &s[4..5] {
                "n" => Some(PieceKind::Knight),
                "b" => Some(PieceKind::Bishop),
                "r" => Some(PieceKind::Rook),
                "q" => Some(PieceKind::Queen),
                _ => None,
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
/// Refer to [`Position::encode_san`](crate::game::position::Position::encode_san) and [`Position::decode_san`](crate::game::position::Position::decode_san) for conversions.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum SanMove {
    PawnMove {
        origin_file: File,
        is_capture: bool,
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
            Self::PawnMove {
                origin_file,
                is_capture,
                target,
                promoting_to,
            } => {
                if is_capture {
                    write!(f, "{origin_file}x")?
                }
                write!(f, "{target}")?;
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
impl std::str::FromStr for SanMove {
    // TODO: parsing errors
    type Err = ();

    fn from_str(_s: &str) -> Result<Self, Self::Err> {
        todo!("SAN parsing is not yet implemented")
    }
}
