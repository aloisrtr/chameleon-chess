//! Piece types encoding.

use super::colour::Colour;

/// Total number of different piece kinds (6).
pub const NUM_PIECES: usize = 6;

/// Complete set of information for identifying a piece.
pub type Piece = (PieceKind, Colour);

/// The kind of a piece, one of Pawn, Knight, Bishop, Rook, Queen or King. Usually
/// with supplementaty information about the color of the piece, in the form of
/// the tuple type [`Piece`].
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
    /// Checks if this piece kind is a diagonal slider (bishops and queens).
    #[inline(always)]
    pub fn is_diagonal_slider(self) -> bool {
        (self as u8 + 3) & 0b101 == 0b101
    }
    /// Checks if this piece kind is an orthogonal slider (rooks and queens).
    #[inline(always)]
    pub fn is_orthogonal_slider(self) -> bool {
        (self as u8 + 3) & 0b110 == 0b110
    }

    /// Iterator over all piece kinds.
    pub fn iter() -> impl Iterator<Item = Self> {
        [
            PieceKind::Pawn,
            PieceKind::Knight,
            PieceKind::Bishop,
            PieceKind::Rook,
            PieceKind::Queen,
            PieceKind::King,
        ]
        .into_iter()
    }

    /// Iterator over all piece kinds except the king.
    pub fn iter_all_but_king() -> impl Iterator<Item = Self> {
        [
            PieceKind::Pawn,
            PieceKind::Knight,
            PieceKind::Bishop,
            PieceKind::Rook,
            PieceKind::Queen,
        ]
        .into_iter()
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
