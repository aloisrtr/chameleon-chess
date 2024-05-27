//! Enumerations of chessboard accessing constants, such as files, ranks and squares.
use crate::bitboard::Bitboard;

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
    /// Fails if the index is more than 7.
    #[inline]
    pub fn from_index(index: u8) -> Option<Self> {
        if index < 8 {
            Some(unsafe { Self::from_index_unchecked(index) })
        } else {
            None
        }
    }

    /// A file from a given index.
    /// # Safety
    /// If the index is more than 7, results in undefined behavior.
    #[inline]
    pub unsafe fn from_index_unchecked(index: u8) -> Self {
        std::mem::transmute(index)
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
impl std::str::FromStr for File {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s.to_ascii_lowercase().as_str() {
            "a" => Self::A,
            "b" => Self::B,
            "c" => Self::C,
            "d" => Self::D,
            "e" => Self::E,
            "f" => Self::F,
            "g" => Self::G,
            "h" => Self::H,
            _ => Err(())?,
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
    /// Fails if the index is more than 7.
    #[inline]
    pub fn from_index(index: u8) -> Option<Self> {
        if index < 8 {
            Some(unsafe { Self::from_index_unchecked(index) })
        } else {
            None
        }
    }

    /// A rank from a given index.
    /// # Safety
    /// If the index is more than 7, results in undefined behavior.
    #[inline]
    pub unsafe fn from_index_unchecked(index: u8) -> Self {
        std::mem::transmute(index)
    }
}
impl std::fmt::Display for Rank {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", 1 + *self as u8)
    }
}
impl std::str::FromStr for Rank {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_index(s.parse::<u8>().map_err(|_| ())? - 1).ok_or(())
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
    /// Instantiates a new square based on file and rank.
    #[inline]
    pub const fn new(file: File, rank: Rank) -> Self {
        unsafe { std::mem::transmute((rank as u8) << 3 | (file as u8)) }
    }

    /// Instantitates a new square from its index.
    ///
    /// Returns `None` if the index is more than 63.
    #[inline]
    pub const fn from_index(index: u8) -> Option<Self> {
        if index < 64 {
            Some(unsafe { Self::from_index_unchecked(index) })
        } else {
            None
        }
    }

    /// Instantitates a new square from its index.
    /// # Safety
    /// If the index is more than 63, causes undefined behavior.
    #[inline]
    pub const unsafe fn from_index_unchecked(index: u8) -> Self {
        std::mem::transmute(index)
    }

    /// Returns the rank of the square.
    #[inline]
    pub const fn rank(self) -> Rank {
        unsafe { std::mem::transmute((self as u8) >> 3) }
    }
    /// Returns the file of the square.
    #[inline]
    pub const fn file(self) -> File {
        unsafe { std::mem::transmute((self as u8) & 7) }
    }

    /// Translates this square by a given delta.
    ///
    /// Returns `None` if the translation would go out of the board.
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
        (0..64).map(|i| unsafe { Square::from_index_unchecked(i) })
    }

    /// An iterator over all square, ordered in big-endian rank/little-endian file.
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
impl std::str::FromStr for Square {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let chars = s.chars().map(|c| c.to_string()).collect::<Vec<_>>();
        if chars.len() != 2 {
            return Err(());
        }
        Ok(Self::new(chars[0].parse()?, chars[1].parse()?))
    }
}

/// Deltas represent directions in which pieces can move.
///
/// They can be added or subtracted to [Square]s to obtain the target of the
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
impl Delta {
    pub const fn pawn_deltas(swapped: bool) -> (Self, Self, Self) {
        if swapped {
            (Self::South, Self::SouthEast, Self::SouthWest)
        } else {
            (Self::North, Self::NorthEast, Self::NorthWest)
        }
    }
}
