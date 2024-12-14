//! Actions are separated in two distinct categories:
//! - [`LegalAction`] are generated by the crate, packed and encoded in a specific way so that making/unmaking them is efficient. They are also necessarily correct to play in the position that generated them.
//! - [`Action`] are user-generated, and are a more verbose way of interacting with the [Position]s API. However, being user-generated, they are not necessarily legal.

use super::{piece::PieceKind, square::Square};

/// Describes a move using a from-to <promotion> approach.
///
/// Moves encoded this way have no guarantee to be correct, let alone legal, and
/// are simply an easier interface with the API.
#[derive(Clone, Copy, Hash, Eq, PartialEq, Debug)]
pub struct Action {
    pub origin: Square,
    pub target: Square,
    pub promotion: Option<PieceKind>,
}
impl Action {
    /// Creates a new move.
    pub fn new(origin: Square, target: Square) -> Self {
        Self {
            origin,
            target,
            promotion: None,
        }
    }

    /// Creates a new promoting move.
    pub fn new_promotion(origin: Square, target: Square, promotion: PieceKind) -> Self {
        Self {
            origin,
            target,
            promotion: Some(promotion),
        }
    }
}
impl From<LegalAction> for Action {
    fn from(value: LegalAction) -> Self {
        value.downgrade()
    }
}
impl std::str::FromStr for Action {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let origin = s[0..2].parse()?;
        let target = s[2..4].parse()?;
        let promotion = s.chars().nth(4).and_then(|c| match c.to_ascii_lowercase() {
            'n' => Some(PieceKind::Knight),
            'b' => Some(PieceKind::Bishop),
            'r' => Some(PieceKind::Rook),
            'q' => Some(PieceKind::Queen),
            _ => None,
        });

        Ok(Self {
            origin,
            target,
            promotion,
        })
    }
}
impl std::fmt::Display for Action {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.origin,
            self.target,
            if let Some(piece_kind) = self.promotion {
                piece_kind.to_string()
            } else {
                String::new()
            }
        )
    }
}

/// Encodes moves that are legal to play on a given position.
///
/// These are not created by users, and one must use a move generator (admitted valid)
/// in order to access this object.
#[derive(Clone, Copy, Hash, Eq, PartialEq, Debug)]
pub struct LegalAction(u16);
impl LegalAction {
    /// Downgrades this legal action to a simple action.
    pub fn downgrade(self) -> Action {
        Action {
            origin: self.origin(),
            target: self.target(),
            promotion: self.is_promotion(),
        }
    }

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

    /// Creates a set of promotions from a pawn push.
    #[inline(always)]
    pub(crate) const fn new_promotion(origin: Square, target: Square) -> [Self; 4] {
        let general_move = origin as u16 | (target as u16) << 6 | Self::PROMOTION;
        [
            Self(general_move),
            Self(general_move | (1 << 12)),
            Self(general_move | (2 << 12)),
            Self(general_move | (3 << 12)),
        ]
    }

    /// Creates a set of promotions from a pawn capture.
    #[inline(always)]
    pub(crate) const fn new_promotion_capture(origin: Square, target: Square) -> [Self; 4] {
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
    pub(crate) const fn new_queenside_castle<const BLACK_TO_MOVE: bool>() -> Self {
        if BLACK_TO_MOVE {
            Self(Square::E8 as u16 | (Square::C8 as u16) << 6 | Self::SPECIAL_0 | Self::SPECIAL_1)
        } else {
            Self(Square::E1 as u16 | (Square::C1 as u16) << 6 | Self::SPECIAL_0 | Self::SPECIAL_1)
        }
    }

    /// Creates an en passant kingside castle move.
    #[inline(always)]
    pub(crate) const fn new_kingside_castle<const BLACK_TO_MOVE: bool>() -> Self {
        if BLACK_TO_MOVE {
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
    pub const fn is_promotion(self) -> Option<PieceKind> {
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
impl std::fmt::Display for LegalAction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}{}",
            self.origin(),
            self.target(),
            if let Some(piece_kind) = self.is_promotion() {
                piece_kind.to_string()
            } else {
                String::new()
            }
        )
    }
}
