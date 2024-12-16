//! # Representation of castling rights

use std::str::FromStr;

use super::{
    colour::Colour,
    zobrist::{CASTLING_RIGHTS_OFFSET, ZOBRIST_KEYS},
};
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct CastlingRights(u8);
impl CastlingRights {
    const KINGSIDE_BLACK: u8 = 0b0001;
    const QUEENSIDE_BLACK: u8 = 0b0010;
    const KINGSIDE_WHITE: u8 = 0b0100;
    const QUEENSIDE_WHITE: u8 = 0b1000;
    const FULL: u8 =
        Self::KINGSIDE_BLACK | Self::KINGSIDE_WHITE | Self::QUEENSIDE_BLACK | Self::QUEENSIDE_WHITE;
    const EMPTY: u8 = 0;

    /// Full castling rights for both sides.
    pub const fn full() -> Self {
        Self(Self::FULL)
    }

    /// No castling rights for any sides.
    pub const fn none() -> Self {
        Self(Self::EMPTY)
    }

    /// Checks if no one can castle.
    pub const fn is_none(self) -> bool {
        self.0 == Self::EMPTY
    }

    /// Checks if queenside castling is allowed for a certain colour.
    #[inline(always)]
    pub const fn kingside_castle_allowed(self, colour: Colour) -> bool {
        if colour.is_black() {
            self.0 & Self::KINGSIDE_BLACK != 0
        } else {
            self.0 & Self::KINGSIDE_WHITE != 0
        }
    }
    /// Checks if kingside castling is allowed for a certain colour.
    #[inline(always)]
    pub const fn queenside_castle_allowed(self, colour: Colour) -> bool {
        if colour.is_black() {
            self.0 & Self::QUEENSIDE_BLACK != 0
        } else {
            self.0 & Self::QUEENSIDE_WHITE != 0
        }
    }

    /// Disallows queenside for a given side.
    #[inline(always)]
    pub fn disallow_kingside_castle(&mut self, colour: Colour) {
        self.0 &= if colour.is_black() {
            !Self::KINGSIDE_BLACK
        } else {
            !Self::KINGSIDE_WHITE
        }
    }
    /// Disallows queenside for a given side.
    #[inline(always)]
    pub fn disallow_queenside_castle(&mut self, colour: Colour) {
        self.0 &= if colour.is_black() {
            !Self::QUEENSIDE_BLACK
        } else {
            !Self::QUEENSIDE_WHITE
        }
    }
    /// Disallows castling for a given side.
    pub fn disallow(&mut self, colour: Colour) {
        self.0 &= if colour.is_black() {
            !(Self::QUEENSIDE_BLACK | Self::KINGSIDE_BLACK)
        } else {
            !(Self::QUEENSIDE_WHITE | Self::KINGSIDE_WHITE)
        }
    }

    /// Returns the Zobrist hash of these castling rights.
    #[inline(always)]
    pub fn zobrist_hash(self) -> u64 {
        let mut hash = 0;
        for i in 0..4 {
            let mask = 1 << i;
            if self.0 & mask != 0 {
                hash ^= ZOBRIST_KEYS[CASTLING_RIGHTS_OFFSET + i]
            }
        }
        hash
    }
}
impl FromStr for CastlingRights {
    type Err = ();
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut rights = 0;
        for c in s.chars() {
            match c {
                'k' => rights |= Self::KINGSIDE_BLACK,
                'q' => rights |= Self::QUEENSIDE_BLACK,
                'K' => rights |= Self::KINGSIDE_WHITE,
                'Q' => rights |= Self::QUEENSIDE_WHITE,
                '-' => return Ok(Self(Self::EMPTY)),
                _ => return Err(()),
            }
        }
        Ok(Self(rights))
    }
}
impl std::fmt::Display for CastlingRights {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_none() {
            return write!(f, "-");
        }

        if self.kingside_castle_allowed(Colour::White) {
            write!(f, "K")?
        }
        if self.queenside_castle_allowed(Colour::White) {
            write!(f, "Q")?
        }
        if self.kingside_castle_allowed(Colour::Black) {
            write!(f, "K")?
        }
        if self.kingside_castle_allowed(Colour::White) {
            write!(f, "q")?
        }
        Ok(())
    }
}
