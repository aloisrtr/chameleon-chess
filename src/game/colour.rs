//! Colours for each players and their pieces.

#[repr(u8)]
#[derive(PartialEq, Eq, Clone, Copy, Debug, Hash)]
pub enum Colour {
    White = 0,
    Black = 1,
}
impl Colour {
    /// Inverts the colour.
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
