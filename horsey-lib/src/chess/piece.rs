//! Piece types encoding.

use std::str::FromStr;

use crate::parsing::PartialFromStr;

use super::colour::Colour;

/// Total number of different piece kinds (6).
pub const NUM_PIECES: usize = 6;

const PIECE_SYMBOLS: [char; 12] = ['P', 'N', 'B', 'R', 'Q', 'K', 'p', 'n', 'b', 'r', 'q', 'k'];
const PIECE_SYMBOLS_UNICODE: [char; 12] =
    ['♙', '♘', '♗', '♖', '♕', '♔', '♟', '♞', '♝', '♜', '♛', '♚'];

/// Complete set of information for identifying a piece (colour and kind).
///
/// # Parsing
/// Pieces can be parsed from their symbol ('p', 'n', 'b', 'r', 'q', 'k' for black,
/// uppercase for white) or unicode symbols (U+2654 to U+2659 for white, U+265A to U+265F for black)
/// using Rust's [`FromStr`] trait.
/// ```
/// # use horsey::chess::piece::*;
/// # use horsey::chess::colour::*;
/// assert_eq!("p".parse(), Ok(Piece::new(PieceKind::Pawn, Colour::Black)));
/// assert_eq!("♕".parse(), Ok(Piece::new(PieceKind::Queen, Colour::White)));
/// ```
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Piece {
    pub kind: PieceKind,
    pub colour: Colour,
}
impl Piece {
    /// Creates a new `kind` piece of the given `colour`.
    pub fn new(kind: PieceKind, colour: Colour) -> Self {
        Self { kind, colour }
    }

    /// Returns the piece's symbol.
    /// # Example
    /// ```
    /// # use horsey::chess::piece::*;
    /// # use horsey::chess::colour::*;
    /// assert_eq!(Piece::new(PieceKind::Pawn, Colour::Black).symbol(), 'p');
    /// ```
    pub fn symbol(&self) -> char {
        PIECE_SYMBOLS[self.colour as usize * 6 + self.kind as usize]
    }

    /// Returns the piece's Unicode symbol.
    /// # Example
    /// ```
    /// # use horsey::chess::piece::*;
    /// # use horsey::chess::colour::*;
    /// assert_eq!(Piece::new(PieceKind::Rook, Colour::Black).unicode_symbol(), '♜');
    /// ```
    pub fn unicode_symbol(&self) -> char {
        PIECE_SYMBOLS_UNICODE[self.colour as usize * 6 + self.kind as usize]
    }
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

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum PieceParseError {
    InvalidPieceSymbol(char),
    EmptyInput,
    InputTooLong,
}
impl std::fmt::Display for PieceParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidPieceSymbol(c) => write!(f, "{c} is not a valid piece symbol"),
            Self::EmptyInput => write!(f, "Empty input"),
            Self::InputTooLong => write!(f, "A piece can only be one character long"),
        }
    }
}
impl std::error::Error for PieceParseError {}

impl PartialFromStr for Piece {
    type Err = PieceParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let symbol = s.chars().next().ok_or(PieceParseError::EmptyInput)?;
        let piece = match symbol {
            'p' | '♟' => Self::new(PieceKind::Pawn, Colour::Black),
            'n' | '♞' => Self::new(PieceKind::Knight, Colour::Black),
            'b' | '♝' => Self::new(PieceKind::Bishop, Colour::Black),
            'r' | '♜' => Self::new(PieceKind::Rook, Colour::Black),
            'q' | '♛' => Self::new(PieceKind::Queen, Colour::Black),
            'k' | '♚' => Self::new(PieceKind::King, Colour::Black),
            'P' | '♙' => Self::new(PieceKind::Pawn, Colour::White),
            'N' | '♘' => Self::new(PieceKind::Knight, Colour::White),
            'B' | '♗' => Self::new(PieceKind::Bishop, Colour::White),
            'R' | '♖' => Self::new(PieceKind::Rook, Colour::White),
            'Q' | '♕' => Self::new(PieceKind::Queen, Colour::White),
            'K' | '♔' => Self::new(PieceKind::King, Colour::White),
            _ => Err(PieceParseError::InvalidPieceSymbol(symbol))?,
        };

        Ok((piece, &s[symbol.len_utf8()..]))
    }
}
impl FromStr for Piece {
    type Err = PieceParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(result, rest)| {
            if rest.is_empty() {
                Ok(result)
            } else {
                Err(PieceParseError::InputTooLong)
            }
        })
    }
}

/// The kind of a piece, one of Pawn, Knight, Bishop, Rook, Queen or King.
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
impl PartialFromStr for PieceKind {
    type Err = PieceParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let symbol = s.chars().next().ok_or(PieceParseError::EmptyInput)?;
        let piece = match symbol {
            'p' | '♟' => PieceKind::Pawn,
            'n' | '♞' => PieceKind::Knight,
            'b' | '♝' => PieceKind::Bishop,
            'r' | '♜' => PieceKind::Rook,
            'q' | '♛' => PieceKind::Queen,
            'k' | '♚' => PieceKind::King,
            'P' | '♙' => PieceKind::Pawn,
            'N' | '♘' => PieceKind::Knight,
            'B' | '♗' => PieceKind::Bishop,
            'R' | '♖' => PieceKind::Rook,
            'Q' | '♕' => PieceKind::Queen,
            'K' | '♔' => PieceKind::King,
            _ => Err(PieceParseError::InvalidPieceSymbol(symbol))?,
        };

        Ok((piece, &s[symbol.len_utf8()..]))
    }
}
impl FromStr for PieceKind {
    type Err = PieceParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(result, rest)| {
            if rest.is_empty() {
                Ok(result)
            } else {
                Err(PieceParseError::InputTooLong)
            }
        })
    }
}

/// Special type that only contains valid promotion targets
/// (knight, bishop, rook and queen).
///
/// This is used to avoid the hassle of testing if we represent invalid state
/// within pawn promotion representations, parsing, etc.
///
/// Methods and trait implementation are made for an easy conversion to the standard
/// [`PieceKind`] type. Most structures using [`PromotionTarget`] to avoid invalid
/// state should return [`PieceKind`] for any method accessing the promotion value.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum PromotionTarget {
    Knight = 1,
    Bishop = 2,
    Rook = 3,
    Queen = 4,
}
impl PromotionTarget {
    /// Converts a piece kind into a promotion target if such a transformation is valid.
    pub fn from_piece_kind(p: PieceKind) -> Option<Self> {
        Option::<Self>::from(p)
    }

    /// Converts this promotion target to the corresponding piece kind.
    pub fn to_piece_kind(self) -> PieceKind {
        PieceKind::from(self)
    }
}
impl From<PieceKind> for Option<PromotionTarget> {
    fn from(value: PieceKind) -> Self {
        if value.is_valid_promotion_target() {
            // SAFETY: The internal representations are sure to match due to `repr(u8)`.
            Some(unsafe { std::mem::transmute(value) })
        } else {
            None
        }
    }
}
impl From<PromotionTarget> for PieceKind {
    fn from(value: PromotionTarget) -> Self {
        // SAFETY: The internal representations are sure to match due to `repr(u8)`.
        unsafe { std::mem::transmute(value) }
    }
}
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum PromotionTargetParseError {
    InvalidPromotionTarget(PieceKind),
    InvalidPieceSymbol(char),
    EmptyInput,
    InputTooLong,
}
impl std::fmt::Display for PromotionTargetParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidPromotionTarget(p) => write!(f, "{p} is not a valid promotion target"),
            Self::InvalidPieceSymbol(c) => write!(f, "{c} is not a valid piece symbol"),
            Self::EmptyInput => write!(f, "Empty input"),
            Self::InputTooLong => write!(f, "A piece can only be one character long"),
        }
    }
}
impl std::error::Error for PromotionTargetParseError {}

impl PartialFromStr for PromotionTarget {
    type Err = PromotionTargetParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let symbol = s
            .chars()
            .next()
            .ok_or(PromotionTargetParseError::EmptyInput)?;
        let piece = match symbol {
            'n' | '♞' => Self::Knight,
            'b' | '♝' => Self::Bishop,
            'r' | '♜' => Self::Rook,
            'q' | '♛' => Self::Queen,
            'N' | '♘' => Self::Knight,
            'B' | '♗' => Self::Bishop,
            'R' | '♖' => Self::Rook,
            'Q' | '♕' => Self::Queen,
            'p' | '♟' => Err(PromotionTargetParseError::InvalidPromotionTarget(
                PieceKind::Pawn,
            ))?,
            'k' | '♚' => Err(PromotionTargetParseError::InvalidPromotionTarget(
                PieceKind::King,
            ))?,
            'P' | '♙' => Err(PromotionTargetParseError::InvalidPromotionTarget(
                PieceKind::Pawn,
            ))?,
            'K' | '♔' => Err(PromotionTargetParseError::InvalidPromotionTarget(
                PieceKind::King,
            ))?,
            _ => Err(PromotionTargetParseError::InvalidPieceSymbol(symbol))?,
        };

        Ok((piece, &s[symbol.len_utf8()..]))
    }
}
impl FromStr for PromotionTarget {
    type Err = PromotionTargetParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(result, rest)| {
            if rest.is_empty() {
                Ok(result)
            } else {
                Err(PromotionTargetParseError::InputTooLong)
            }
        })
    }
}
impl std::fmt::Display for PromotionTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_piece_kind())
    }
}
