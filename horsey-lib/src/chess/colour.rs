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
    /// # Example
    /// ```
    /// # use horsey::chess::colour::Colour;
    /// let mut side_to_move = Colour::White;
    /// side_to_move.invert();
    /// assert_eq!(side_to_move, Colour::Black);
    /// ```
    #[inline]
    pub fn invert(&mut self) {
        *self = if self.is_black() {
            Colour::White
        } else {
            Colour::Black
        }
    }

    /// Returns the inverse of this colour.
    /// # Example
    /// ```
    /// # use horsey::chess::colour::Colour;
    /// assert_eq!(Colour::White.inverse(), Colour::Black);
    /// ```
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
impl std::fmt::Display for Colour {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.is_black() { "Black" } else { "White" })
    }
}
impl From<bool> for Colour {
    fn from(value: bool) -> Self {
        if value { Self::Black } else { Self::White }
    }
}
impl From<&bool> for Colour {
    fn from(value: &bool) -> Self {
        Self::from(*value)
    }
}
