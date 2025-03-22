//! Colours for each players and their pieces.

/// Number of different colours (2).
pub const NUM_COLOURS: usize = 2;

/// Colour enumeration.
#[repr(u8)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Debug, Hash)]
pub enum Colour {
    White = 0,
    Black = 1,
}
impl Colour {
    /// Inverts the colour in place.
    #[inline]
    pub fn invert(&mut self) {
        *self = if self.is_black() {
            Colour::White
        } else {
            Colour::Black
        }
    }

    /// Returns the inverse of this colour.
    #[inline]
    pub const fn inverse(&self) -> Self {
        if self.is_black() {
            Colour::White
        } else {
            Colour::Black
        }
    }

    /// Checks if the colour variant is white.
    #[inline]
    pub const fn is_white(&self) -> bool {
        matches!(self, Colour::White)
    }

    /// Checks if the colour variant is black.
    #[inline]
    pub const fn is_black(&self) -> bool {
        matches!(self, Colour::Black)
    }
}
impl From<bool> for Colour {
    fn from(value: bool) -> Self {
        if value {
            Self::Black
        } else {
            Self::White
        }
    }
}
impl From<&bool> for Colour {
    fn from(value: &bool) -> Self {
        Self::from(*value)
    }
}
