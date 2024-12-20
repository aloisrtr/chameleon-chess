//! # Actions (or moves)

use super::{
    colour::Colour,
    piece::PieceKind,
    square::{File, Rank, Square},
};

/// Describes a move using a from-to \<promotion\> approach, with all relevant
/// information.
#[derive(Clone, Copy, Hash, Eq, PartialEq, Debug)]
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
    pub const fn new_quiet(origin: Square, target: Square) -> Self {
        Self(origin as u16 | (target as u16) << 6)
    }

    /// Creates a new capture.
    #[inline(always)]
    pub const fn new_capture(origin: Square, target: Square) -> Self {
        Self(origin as u16 | (target as u16) << 6 | Self::CAPTURE)
    }

    /// Creates a new double push.
    #[inline(always)]
    pub const fn new_double_push(origin: Square, target: Square) -> Self {
        Self(origin as u16 | (target as u16) << 6 | Self::SPECIAL_0)
    }

    /// Returns a new promoting move.
    pub const fn new_promotion(origin: Square, target: Square, promoting_to: PieceKind) -> Self {
        Self(
            origin as u16
                | (target as u16) << 6
                | Self::PROMOTION
                | (promoting_to as u16 - PieceKind::Knight as u16) << 12,
        )
    }

    /// Creates a set of promotions from a pawn push.
    #[inline(always)]
    pub const fn new_promotions(origin: Square, target: Square) -> [Self; 4] {
        let general_move = origin as u16 | (target as u16) << 6 | Self::PROMOTION;
        [
            Self(general_move),
            Self(general_move | (1 << 12)),
            Self(general_move | (2 << 12)),
            Self(general_move | (3 << 12)),
        ]
    }

    /// Returns a new promoting move with capture.
    pub const fn new_promotion_capture(
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
    pub const fn new_promotion_captures(origin: Square, target: Square) -> [Self; 4] {
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
    pub const fn new_en_passant(origin: Square, target: Square) -> Self {
        Self(origin as u16 | (target as u16) << 6 | Self::CAPTURE | Self::SPECIAL_0)
    }

    /// Creates an en passant queenside castle move.
    #[inline(always)]
    pub const fn new_queenside_castle(side: Colour) -> Self {
        if side.is_black() {
            Self(Square::E8 as u16 | (Square::C8 as u16) << 6 | Self::SPECIAL_0 | Self::SPECIAL_1)
        } else {
            Self(Square::E1 as u16 | (Square::C1 as u16) << 6 | Self::SPECIAL_0 | Self::SPECIAL_1)
        }
    }

    /// Creates an en passant kingside castle move.
    #[inline(always)]
    pub const fn new_kingside_castle(side: Colour) -> Self {
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
    pub const fn is_queenside_castle(self) -> bool {
        self.promotion_target().is_none()
            && !self.is_capture()
            && self.special_1_is_set()
            && self.special_0_is_set()
    }

    /// Checks if this move encodes a kingside castle.
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

/// Pure coordinate notation move, mainly used for parsing UCI.
///
/// These can be passed to a [`Position`] instance to convert them into usable moves.
#[derive(Clone, Copy, Hash, Eq, PartialEq, Debug)]
pub struct PcnMove {
    pub from: Square,
    pub to: Square,
    pub promoting_to: Option<PieceKind>,
}
impl std::fmt::Display for PcnMove {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.from, self.to)?;
        if let Some(kind) = self.promoting_to {
            write!(f, "{kind}")?
        }
        Ok(())
    }
}
impl std::str::FromStr for PcnMove {
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
            from,
            to,
            promoting_to,
        })
    }
}

/// Standard Algebraic Notation encoded move, mainly for use in Portable Game Notation
/// and/or for human-readability (in UCI debug mode for example).
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
