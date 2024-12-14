/// Colours for each player.
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
        *self = if *self == Colour::Black {
            Colour::White
        } else {
            Colour::Black
        }
    }

    /// Returns the inverse of this colour.
    #[inline]
    pub fn inverse(&self) -> Self {
        if *self == Colour::Black {
            Colour::White
        } else {
            Colour::Black
        }
    }

    /// Checks if the colour variant is white.
    #[inline]
    pub fn is_white(&self) -> bool {
        *self == Colour::White
    }

    /// Checks if the colour variant is black.
    #[inline]
    pub fn is_black(&self) -> bool {
        *self == Colour::Black
    }
}
