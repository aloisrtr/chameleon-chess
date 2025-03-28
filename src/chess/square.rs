//! Enumerations of chessboard accessing constants, such as files, ranks and squares.
use thiserror::Error;

use crate::parsing::PartialFromStr;

use super::bitboard::Bitboard;

/// Files of a chessboard (A-H).
#[repr(u8)]
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum File {
    A,
    B,
    C,
    D,
    E,
    F,
    G,
    H,
}
impl File {
    /// Returns the set of all squares within a given file as a bitboard.
    #[inline]
    pub(crate) const fn bitboard(self) -> Bitboard {
        match self {
            Self::A => Bitboard(0x0101010101010101),
            Self::B => Bitboard(0x0202020202020202),
            Self::C => Bitboard(0x0404040404040404),
            Self::D => Bitboard(0x0808080808080808),
            Self::E => Bitboard(0x1010101010101010),
            Self::F => Bitboard(0x2020202020202020),
            Self::G => Bitboard(0x4040404040404040),
            Self::H => Bitboard(0x8080808080808080),
        }
    }

    /// A file from a given index.
    ///
    /// Returns [`None`] if the index is more than 7.
    ///
    /// # Exemple
    /// ```
    /// # use horsey::chess::square::*;
    /// assert_eq!(File::from_index(2), Some(File::C));
    /// assert!(File::from_index(10).is_none());
    /// ```
    #[inline]
    pub fn from_index(index: u8) -> Option<Self> {
        if index < 8 {
            Some(unsafe { Self::from_index_unchecked(index) })
        } else {
            None
        }
    }

    /// A file from a given index.
    ///
    /// # Safety
    /// If the index is more than 7, results in undefined behavior.
    ///
    /// # Exemple
    /// ```
    /// # use horsey::chess::square::*;
    /// assert_eq!(unsafe { File::from_index_unchecked(2) }, File::C);
    /// ```
    #[inline]
    pub unsafe fn from_index_unchecked(index: u8) -> Self {
        std::mem::transmute(index)
    }

    /// The index of this file.
    /// # Exemple
    /// ```
    /// # use horsey::chess::square::*;
    /// assert_eq!(File::C.as_index(), 2);
    /// ```
    pub fn as_index(self) -> u8 {
        self as u8
    }
}
impl std::ops::Add<Delta> for File {
    type Output = File;

    fn add(self, rhs: Delta) -> Self::Output {
        let delta_file = (rhs as i8).rem_euclid(8);
        unsafe { std::mem::transmute((self as u8).wrapping_add_signed(delta_file)) }
    }
}
impl std::ops::AddAssign<Delta> for File {
    fn add_assign(&mut self, rhs: Delta) {
        *self = *self + rhs
    }
}
impl std::ops::Sub<Delta> for File {
    type Output = File;

    fn sub(self, rhs: Delta) -> Self::Output {
        let delta_file = (rhs as i8).rem_euclid(8);
        unsafe { std::mem::transmute((self as u8).wrapping_add_signed(-delta_file)) }
    }
}
impl std::ops::SubAssign<Delta> for File {
    fn sub_assign(&mut self, rhs: Delta) {
        *self = *self - rhs
    }
}
impl std::fmt::Display for File {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Self::A => 'a',
                Self::B => 'b',
                Self::C => 'c',
                Self::D => 'd',
                Self::E => 'e',
                Self::F => 'f',
                Self::G => 'g',
                Self::H => 'h',
            }
        )
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Error)]
pub enum FileParseError {
    #[error("{0} does not denote a valid chessboard file")]
    InvalidFileSymbol(char),
    #[error("Cannot parse a file from an empty input")]
    EmptyInput,
    #[error("A file cannot be more than one character")]
    InputTooLong,
}
impl PartialFromStr for File {
    type Err = FileParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let symbol = s.chars().next().ok_or(FileParseError::EmptyInput)?;
        let file = match symbol.to_ascii_lowercase() {
            'a' => Self::A,
            'b' => Self::B,
            'c' => Self::C,
            'd' => Self::D,
            'e' => Self::E,
            'f' => Self::F,
            'g' => Self::G,
            'h' => Self::H,
            _ => Err(FileParseError::InvalidFileSymbol(symbol))?,
        };

        Ok((file, &s[1..]))
    }
}
impl std::str::FromStr for File {
    type Err = FileParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(result, rest)| {
            if rest.is_empty() {
                Ok(result)
            } else {
                Err(FileParseError::InputTooLong)
            }
        })
    }
}

/// Ranks of a chessboard (1-8).
#[repr(u8)]
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Rank {
    One,
    Two,
    Three,
    Four,
    Five,
    Six,
    Seven,
    Eight,
}
impl Rank {
    /// Returns the set of all squares within a given rank as a bitboard.
    #[inline]
    pub(crate) const fn bitboard(self) -> Bitboard {
        match self {
            Self::One => Bitboard(0x00000000000000FF),
            Self::Two => Bitboard(0x000000000000FF00),
            Self::Three => Bitboard(0x0000000000FF0000),
            Self::Four => Bitboard(0x00000000FF000000),
            Self::Five => Bitboard(0x000000FF00000000),
            Self::Six => Bitboard(0x0000FF0000000000),
            Self::Seven => Bitboard(0x00FF000000000000),
            Self::Eight => Bitboard(0xFF00000000000000),
        }
    }

    /// A rank from a given index.
    ///
    /// Returns [`None`] if the index is more than 7.
    ///
    /// # Exemple
    /// ```
    /// # use horsey::chess::square::*;
    ///
    /// assert_eq!(Rank::from_index(4), Some(Rank::Five));
    /// assert!(Rank::from_index(12).is_none());
    /// ```
    #[inline]
    pub fn from_index(index: u8) -> Option<Self> {
        if index < 8 {
            Some(unsafe { Self::from_index_unchecked(index) })
        } else {
            None
        }
    }

    /// A rank from a given index.
    ///
    /// # Safety
    /// If the index is more than 7, results in undefined behavior.
    ///
    /// # Example
    /// ```
    /// # use horsey::chess::square::*;
    /// assert_eq!(unsafe { Rank::from_index_unchecked(4) },Rank::Five);
    /// ```
    #[inline]
    pub unsafe fn from_index_unchecked(index: u8) -> Self {
        std::mem::transmute(index)
    }

    /// The index of this rank.
    /// # Example
    /// ```
    /// # use horsey::chess::square::*;
    /// assert_eq!(Rank::Five.as_index(), 4);
    /// ```
    pub fn as_index(self) -> u8 {
        self as u8
    }
}
impl std::ops::Add<Delta> for Rank {
    type Output = Rank;

    fn add(self, rhs: Delta) -> Self::Output {
        let delta_rank = (rhs as i8) / 8;
        unsafe { std::mem::transmute((self as u8).wrapping_add_signed(delta_rank)) }
    }
}
impl std::ops::AddAssign<Delta> for Rank {
    fn add_assign(&mut self, rhs: Delta) {
        *self = *self + rhs
    }
}
impl std::ops::Sub<Delta> for Rank {
    type Output = Rank;

    fn sub(self, rhs: Delta) -> Self::Output {
        let delta_rank = (rhs as i8) / 8;
        unsafe { std::mem::transmute((self as u8).wrapping_add_signed(-delta_rank)) }
    }
}
impl std::ops::SubAssign<Delta> for Rank {
    fn sub_assign(&mut self, rhs: Delta) {
        *self = *self - rhs
    }
}
impl std::fmt::Display for Rank {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", 1 + *self as u8)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Error)]
pub enum RankParseError {
    #[error("{0} does not denote a valid chessboard rank")]
    InvalidRankSymbol(char),
    #[error("Cannot parse a rank from an empty input")]
    EmptyInput,
    #[error("A rank cannot be more than one character")]
    InputTooLong,
}
impl PartialFromStr for Rank {
    type Err = RankParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let symbol = s.chars().next().ok_or(RankParseError::EmptyInput)?;
        let rank = symbol
            .to_digit(10)
            .and_then(|i| Self::from_index(i.wrapping_sub(1) as u8))
            .ok_or(RankParseError::InvalidRankSymbol(symbol))?;
        Ok((rank, &s[symbol.len_utf8()..]))
    }
}
impl std::str::FromStr for Rank {
    type Err = RankParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(result, rest)| {
            if rest.is_empty() {
                Ok(result)
            } else {
                Err(RankParseError::InputTooLong)
            }
        })
    }
}

/// General square indexing for 8x8 bitboards.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum Square {
    A1,
    B1,
    C1,
    D1,
    E1,
    F1,
    G1,
    H1,
    A2,
    B2,
    C2,
    D2,
    E2,
    F2,
    G2,
    H2,
    A3,
    B3,
    C3,
    D3,
    E3,
    F3,
    G3,
    H3,
    A4,
    B4,
    C4,
    D4,
    E4,
    F4,
    G4,
    H4,
    A5,
    B5,
    C5,
    D5,
    E5,
    F5,
    G5,
    H5,
    A6,
    B6,
    C6,
    D6,
    E6,
    F6,
    G6,
    H6,
    A7,
    B7,
    C7,
    D7,
    E7,
    F7,
    G7,
    H7,
    A8,
    B8,
    C8,
    D8,
    E8,
    F8,
    G8,
    H8,
}
impl Square {
    pub(crate) const DARK_SQUARES: Bitboard = Bitboard(0xaa55aa55aa55aa55);
    #[allow(dead_code)]
    pub(crate) const WHITE_SQUARES: Bitboard = Bitboard(0x55aa55aa55aa55aa);

    /// Array containing all squares in little-endian rank mapping.
    pub const SQUARES: [Square; 64] = {
        let mut squares = [Square::A1; 64];
        let mut i = 0;
        while i < 64 {
            squares[i] = unsafe { Square::from_index_unchecked(i as u8) };
            i += 1;
        }
        squares
    };

    /// Instantiates a new square based on file and rank.
    /// # Example
    /// ```
    /// # use horsey::chess::square::*;
    /// assert_eq!(Square::new(File::A, Rank::Four), Square::A4);
    /// ```
    #[inline]
    pub const fn new(file: File, rank: Rank) -> Self {
        unsafe { std::mem::transmute((rank as u8) << 3 | (file as u8)) }
    }

    /// Instantitates a new square from its index.
    ///
    /// Returns [`None`] if the index is more than 63.
    ///
    /// # Example
    /// ```
    /// # use horsey::chess::square::*;
    /// assert_eq!(Square::from_index(4), Some(Square::E1));
    /// ```
    #[inline]
    pub const fn from_index(index: u8) -> Option<Self> {
        if index < 64 {
            Some(unsafe { Self::from_index_unchecked(index) })
        } else {
            None
        }
    }

    /// Returns the index of this square between 0 and 64, in little-endian rank-file mapping.
    ///
    /// # Example
    /// ```
    /// # use horsey::chess::square::*;
    /// assert_eq!(Square::E5.as_index(), 36);
    /// ```
    #[inline]
    pub const fn as_index(self) -> u8 {
        self as u8
    }

    /// Instantitates a new square from its index.
    ///
    /// # Safety
    /// If the index is more than 63, causes undefined behavior.
    #[inline]
    pub const unsafe fn from_index_unchecked(index: u8) -> Self {
        std::mem::transmute(index)
    }

    /// Returns the rank of the square.
    /// # Example
    /// ```
    /// # use horsey::chess::square::*;
    /// assert_eq!(Square::A4.rank(), Rank::Four);
    /// ```
    #[inline]
    pub const fn rank(self) -> Rank {
        unsafe { std::mem::transmute((self as u8) >> 3) }
    }

    /// Returns the file of the square.
    /// # Example
    /// ```
    /// # use horsey::chess::square::*;
    /// assert_eq!(Square::A4.file(), File::A);
    /// ```
    #[inline]
    pub const fn file(self) -> File {
        unsafe { std::mem::transmute((self as u8) & 7) }
    }

    /// Translates this square by a given delta.
    ///
    /// Returns [`None`] if the translation would go out of the board.
    ///
    /// # Example
    /// ```
    /// # use horsey::chess::square::*;
    /// let square = Square::E1;
    /// assert_eq!(square.translate(Delta::North), Some(Square::E2));
    /// assert!(square.translate(Delta::South).is_none());
    /// ```
    #[inline]
    pub const fn translate(self, delta: Delta) -> Option<Self> {
        if match delta {
            Delta::North => (self.rank() as usize) < 7,
            Delta::South => (self.rank() as usize) > 0,
            Delta::East => (self.file() as usize) < 7,
            Delta::West => (self.file() as usize) > 0,
            Delta::NorthEast => (self.file() as usize) < 7 && (self.rank() as usize) < 7,
            Delta::NorthWest => (self.file() as usize) > 0 && (self.rank() as usize) < 7,
            Delta::SouthEast => (self.file() as usize) < 7 && (self.rank() as usize) > 0,
            Delta::SouthWest => (self.file() as usize) > 0 && (self.rank() as usize) > 0,

            Delta::KnightNorthEast => (self.file() as usize) < 7 && (self.rank() as usize) < 6,
            Delta::KnightNorthWest => (self.file() as usize) > 0 && (self.rank() as usize) < 6,
            Delta::KnightSouthEast => (self.file() as usize) < 7 && (self.rank() as usize) > 1,
            Delta::KnightSouthWest => (self.file() as usize) > 0 && (self.rank() as usize) > 1,
            Delta::KnightEastNorth => (self.file() as usize) < 6 && (self.rank() as usize) < 7,
            Delta::KnightWestNorth => (self.file() as usize) > 1 && (self.rank() as usize) < 7,
            Delta::KnightEastSouth => (self.file() as usize) < 6 && (self.rank() as usize) > 0,
            Delta::KnightWestSouth => (self.file() as usize) > 1 && (self.rank() as usize) > 0,
        } {
            Some(unsafe { self.translate_unchecked(delta) })
        } else {
            None
        }
    }

    /// Translates this square by a given delta.
    /// # Safety
    /// Doing a translation that would result in an out of board square is
    /// undefined behavior.
    #[inline]
    pub const unsafe fn translate_unchecked(self, delta: Delta) -> Self {
        std::mem::transmute((self as u8).wrapping_add_signed(delta as i8))
    }

    /// An iterator over all squares, ordered from A1 to H8.
    pub fn squares_iter() -> impl Iterator<Item = Self> {
        Square::SQUARES.into_iter()
    }

    /// An iterator over all square, ordered in big-endian rank/little-endian file
    /// (equivalent to how squares are ordered in a FEN string).
    pub fn squares_fen_iter() -> impl Iterator<Item = Self> {
        (0..8).rev().flat_map(|rank| {
            (0..8).map(move |file| unsafe {
                let rank = Rank::from_index_unchecked(rank);
                let file = File::from_index_unchecked(file);
                Square::new(file, rank)
            })
        })
    }

    /// Returns a bitboard containing only this square.
    #[inline]
    pub(crate) const fn bitboard(self) -> Bitboard {
        Bitboard(1 << (self as u8))
    }
}
impl std::ops::Add<Delta> for Square {
    type Output = Square;

    fn add(self, rhs: Delta) -> Self::Output {
        unsafe { std::mem::transmute((self as u8).wrapping_add_signed(rhs as i8)) }
    }
}
impl std::ops::AddAssign<Delta> for Square {
    fn add_assign(&mut self, rhs: Delta) {
        *self = *self + rhs
    }
}
impl std::ops::Sub<Delta> for Square {
    type Output = Square;

    fn sub(self, rhs: Delta) -> Self::Output {
        unsafe { std::mem::transmute((self as u8).wrapping_add_signed(-(rhs as i8))) }
    }
}
impl std::ops::SubAssign<Delta> for Square {
    fn sub_assign(&mut self, rhs: Delta) {
        *self = *self - rhs
    }
}
impl std::fmt::Display for Square {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.file(), self.rank())
    }
}

#[derive(Copy, Clone, PartialEq, PartialOrd, Ord, Eq, Debug, Error)]
pub enum SquareParseError {
    #[error(transparent)]
    InvalidFile(#[from] FileParseError),
    #[error(transparent)]
    InvalidRank(#[from] RankParseError),
    #[error("A square cannot be more than two characters long")]
    InputTooLong,
}
impl PartialFromStr for Square {
    type Err = SquareParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let (file, s) = File::partial_from_str(s)?;
        let (rank, s) = Rank::partial_from_str(s)?;
        Ok((Square::new(file, rank), s))
    }
}
impl std::str::FromStr for Square {
    type Err = SquareParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(result, rest)| {
            if rest.is_empty() {
                Ok(result)
            } else {
                Err(SquareParseError::InputTooLong)
            }
        })
    }
}

/// Deltas represent directions in which pieces can move.
///
/// They can be added or subtracted to a [`Square`] to obtain the target of the
/// translation following this delta.
#[repr(i8)]
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub enum Delta {
    North = 8,
    South = -8,
    East = 1,
    West = -1,

    NorthEast = 9,
    NorthWest = 7,
    SouthEast = -7,
    SouthWest = -9,

    KnightNorthEast = 17,
    KnightNorthWest = 15,
    KnightSouthEast = -15,
    KnightSouthWest = -17,
    KnightEastNorth = 10,
    KnightWestNorth = 6,
    KnightEastSouth = -6,
    KnightWestSouth = -10,
}
impl Delta {
    /// Deltas used by knight moves.
    pub const KNIGHT_DELTAS: [Self; 8] = [
        Self::KnightNorthEast,
        Self::KnightNorthWest,
        Self::KnightSouthEast,
        Self::KnightSouthWest,
        Self::KnightEastNorth,
        Self::KnightWestNorth,
        Self::KnightEastSouth,
        Self::KnightWestSouth,
    ];

    /// Deltas in all cardinal directions, which corresponds to queen moves.
    ///
    /// The first half of these are orthogonal deltas (rooks), while the rest
    /// are diagonal (bishops).
    pub const QUEEN_DELTAS: [Self; 8] = [
        Self::North,
        Self::South,
        Self::East,
        Self::West,
        Self::NorthEast,
        Self::NorthWest,
        Self::SouthEast,
        Self::SouthWest,
    ];
}
