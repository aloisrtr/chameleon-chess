/// Existing types of pieces.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum PieceKind {
    Pawn = 0,
    Knight = 1,
    Bishop = 2,
    Rook = 3,
    Queen = 4,
    King = 5,
}
impl PieceKind {
    /// Checks if this piece kind is a diagonal slider.
    #[inline(always)]
    pub fn is_diagonal_slider(self) -> bool {
        (self as u8 + 3) & 0b101 == 0b101
    }
    /// Checks if this piece kind is an orthogonal slider.
    #[inline(always)]
    pub fn is_orthogonal_slider(self) -> bool {
        (self as u8 + 3) & 0b110 == 0b110
    }
}
impl std::fmt::Display for PieceKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::Pawn => 'p',
                Self::Knight => 'n',
                Self::Bishop => 'b',
                Self::Rook => 'r',
                Self::Queen => 'q',
                Self::King => 'k',
            }
        )
    }
}
