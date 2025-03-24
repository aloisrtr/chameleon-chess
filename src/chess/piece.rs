//! Piece types encoding.

use std::str::FromStr;

use thiserror::Error;

use super::colour::Colour;

/// Total number of different piece kinds (6).
pub const NUM_PIECES: usize = 6;

const PIECE_SYMBOLS: [char; 12] = ['P', 'N', 'B', 'R', 'Q', 'K', 'p', 'n', 'b', 'r', 'q', 'k'];

/// Complete set of information for identifying a piece.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Piece {
    pub kind: PieceKind,
    pub colour: Colour,
}
impl std::fmt::Display for Piece {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            PIECE_SYMBOLS[self.colour as usize * 6 + self.kind as usize]
        )
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Error)]
#[error("Invalid piece symbol")]
pub struct PieceParseError;

impl FromStr for Piece {
    type Err = PieceParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let kind = match s.to_ascii_lowercase().as_str() {
            "p" => PieceKind::Pawn,
            "n" => PieceKind::Knight,
            "b" => PieceKind::Bishop,
            "r" => PieceKind::Rook,
            "q" => PieceKind::Queen,
            "k" => PieceKind::King,
            _ => Err(PieceParseError)?,
        };
        Ok(Self {
            kind,
            colour: s.chars().next().unwrap().is_uppercase().into(),
        })
    }
}

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
    /// All piece kinds.
    pub const PIECE_KINDS: [Self; 6] = [
        PieceKind::Pawn,
        PieceKind::Knight,
        PieceKind::Bishop,
        PieceKind::Rook,
        PieceKind::Queen,
        PieceKind::King,
    ];

    /// All pieces but kings.
    pub const NON_KING: [Self; 5] = [
        PieceKind::Pawn,
        PieceKind::Knight,
        PieceKind::Bishop,
        PieceKind::Rook,
        PieceKind::Queen,
    ];

    /// Only minor pieces (knights and bishops).
    pub const MINOR_PIECES: [Self; 2] = [Self::Knight, Self::Bishop];

    /// Pieces that a pawn can promote to.
    pub const PROMOTION_TARGETS: [Self; 4] = [
        PieceKind::Knight,
        PieceKind::Bishop,
        PieceKind::Rook,
        PieceKind::Queen,
    ];

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
        Self::PIECE_KINDS.into_iter()
    }

    /// Iterator over all piece kinds except the king.
    pub fn iter_all_but_king() -> impl Iterator<Item = Self> {
        Self::NON_KING.into_iter()
    }

    /// Checks if this piece kind can be promoted to.
    ///
    /// Returns true for all pieces but pawns and kings.
    pub fn is_valid_promotion_target(&self) -> bool {
        !matches!(self, PieceKind::Pawn | PieceKind::King)
    }
}
impl std::fmt::Display for PieceKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", PIECE_SYMBOLS[*self as usize])
    }
}
