//! # Representation of sets of squares.
//! Bitboards are an efficient way to represent sets of squares,
//! and are used extensively in the board representation.

use std::iter::FusedIterator;

use super::square::{Delta, Rank, Square};

/// Bitboards are data structures used to efficiently represent a set of squares.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash, Default)]
pub struct Bitboard(pub(crate) u64);

impl Bitboard {
    /// The empty bitboard.
    pub const EMPTY: Self = Self(0);
    /// The full (universe) bitboard.
    pub const UNIVERSE: Self = Self(u64::MAX);

    /// Returns an empty bitboard.
    #[inline]
    pub const fn empty() -> Self {
        Self::EMPTY
    }

    /// Returns the universal set (contains all squares).
    #[inline]
    pub const fn universe() -> Self {
        Self::UNIVERSE
    }

    /// Checks if a bitboard is empty.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// assert!(Bitboard::empty().is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.0 == 0
    }

    /// Checks if a bitboard has one or more bits set.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// assert!(Bitboard::universe().is_not_empty());
    /// ```
    #[inline]
    pub const fn is_not_empty(&self) -> bool {
        self.0 != 0
    }

    /// Adds a square to the set.
    #[inline]
    pub const fn insert(&mut self, square: Square) {
        self.0 |= square.bitboard().0
    }

    /// Removes a square from the set.
    #[inline]
    pub const fn remove(&mut self, square: Square) {
        self.0 &= !square.bitboard().0
    }

    /// Toggles a square (if it was present it is removed and vice-versa).
    #[inline]
    pub const fn toggle(&mut self, square: Square) {
        self.0 ^= square.bitboard().0
    }

    /// Checks if a given square is set on the bitboard.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let bb = Bitboard::from_iter([Square::E5, Square::D7]);
    /// assert!(bb.is_set(Square::E5));
    /// assert!(!bb.is_set(Square::E6));
    /// ```
    #[inline]
    pub const fn is_set(&self, square: Square) -> bool {
        self.intersects(square.bitboard())
    }

    /// Checks if a bitboard contains exactly one element.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let bb = Bitboard::from_iter([Square::E5]);
    /// assert!(bb.is_single_populated());
    /// ```
    #[inline]
    pub const fn is_single_populated(&self) -> bool {
        self.0.is_power_of_two()
    }

    /// Checks if a bitboard contains zero or one elements.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let bb = Bitboard::from_iter([Square::E5]);
    /// assert!(bb.has_at_most_one());
    /// assert!(Bitboard::empty().has_at_most_one());
    /// ```
    #[inline]
    pub const fn has_at_most_one(&self) -> bool {
        (self.0 & self.0.wrapping_sub(1)) == 0
    }

    /// Checks if a bitboard has more than one element.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let bb = Bitboard::from_iter([Square::E5]);
    /// assert!(!bb.has_more_than_one());
    /// let bb = Bitboard::from_iter([Square::E5, Square::D7]);
    /// assert!(bb.has_more_than_one());
    /// ```
    #[inline]
    pub const fn has_more_than_one(&self) -> bool {
        (self.0 & self.0.wrapping_sub(1)) != 0
    }

    /// Returns the cardinality of the bitboard (i.e. how many squares are set).
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let bb = Bitboard::from_iter([Square::E5, Square::D7]);
    /// assert_eq!(bb.len(), 2);
    /// assert_eq!(Bitboard::empty().len(), 0);
    /// assert_eq!(Bitboard::universe().len(), 64);
    /// ```
    #[inline]
    pub const fn len(&self) -> u8 {
        self.0.count_ones() as u8
    }

    /// Returns the lowest square in the bitboard.
    ///
    /// If the bitboard is empty, returns `None`.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let bb = Bitboard::from_iter([Square::E5, Square::D7]);
    /// assert_eq!(bb.lowest_square(), Some(Square::E5));
    /// assert_eq!(Bitboard::empty().lowest_square(), None);
    /// ```
    #[inline]
    pub const fn lowest_square(&self) -> Option<Square> {
        if !self.is_empty() {
            Some(unsafe { self.lowest_square_unchecked() })
        } else {
            None
        }
    }

    /// Returns the lowest square in the bitboard.
    ///
    /// # Safety
    /// If passed an empty bitboard, the square will not contain a correct value (undefined behavior).
    #[inline]
    pub const unsafe fn lowest_square_unchecked(&self) -> Square {
        unsafe { Square::from_index_unchecked(self.0.trailing_zeros() as u8) }
    }

    /// Pops the lowest square in the bitboard.
    ///
    /// If the bitboard is empty, returns `None`.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let mut bb = Bitboard::from_iter([Square::E5, Square::D7]);
    /// assert_eq!(bb.pop_lowest_square(), Some(Square::E5));
    /// assert_eq!(bb.pop_lowest_square(), Some(Square::D7));
    /// assert_eq!(bb.pop_lowest_square(), None);
    /// ```
    #[inline]
    pub fn pop_lowest_square(&mut self) -> Option<Square> {
        if !Bitboard::is_empty(self) {
            Some(unsafe { self.pop_lowest_square_unchecked() })
        } else {
            None
        }
    }

    /// Pops the lowest square in the bitboard.
    ///
    /// # Safety
    /// If passed an empty bitboard, the square will not contain a correct value (undefined behavior).
    #[inline]
    pub unsafe fn pop_lowest_square_unchecked(&mut self) -> Square {
        let square = unsafe { self.lowest_square_unchecked() };
        self.0 &= self.0.wrapping_sub(1);
        square
    }

    /// Returns the highest square in the bitboard.
    ///
    /// If the bitboard is empty, returns `None`.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let bb = Bitboard::from_iter([Square::E5, Square::D7]);
    /// assert_eq!(bb.highest_square(), Some(Square::D7));
    /// assert_eq!(Bitboard::empty().highest_square(), None);
    /// ```
    #[inline]
    pub const fn highest_square(&self) -> Option<Square> {
        if !self.is_empty() {
            Some(unsafe { self.highest_square_unchecked() })
        } else {
            None
        }
    }

    /// Returns the highest square in the bitboard.
    /// # Safety
    /// If passed an empty bitboard, the returned index will be 64 (out of bounds thus not usable)
    #[inline]
    pub const unsafe fn highest_square_unchecked(&self) -> Square {
        unsafe { Square::from_index_unchecked(63 - self.0.leading_zeros() as u8) }
    }

    /// Pops the highest square in the bitboard.
    ///
    /// If the bitboard is empty, returns `None`.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let mut bb = Bitboard::from_iter([Square::E5, Square::D7]);
    /// assert_eq!(bb.pop_highest_square(), Some(Square::D7));
    /// assert_eq!(bb.pop_highest_square(), Some(Square::E5));
    /// assert_eq!(bb.pop_highest_square(), None);
    /// ```
    #[inline]
    pub fn pop_highest_square(&mut self) -> Option<Square> {
        if !Bitboard::is_empty(self) {
            Some(unsafe { self.pop_highest_square_unchecked() })
        } else {
            None
        }
    }

    /// Pops the highest square in the bitboard.
    ///
    /// # Safety
    /// If passed an empty bitboard, the returned index will be 64 (out of bounds thus not usable)
    #[inline]
    pub unsafe fn pop_highest_square_unchecked(&mut self) -> Square {
        let square = unsafe { self.highest_square_unchecked() };
        *self ^= square.bitboard();
        square
    }

    /// Rotates the bitboard. This can be thought of as "looking at it from the
    /// opponent's perspective".
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let mut bb = Bitboard::from_iter([Square::E5, Square::D7]);
    /// let rotated_squares = bb.rotate().into_iter().collect::<Vec<_>>();
    /// assert_eq!(rotated_squares, vec![Square::D2, Square::E4])
    /// ```
    #[inline]
    pub fn rotate(&self) -> Self {
        Self(self.0.swap_bytes())
    }

    /// Returns `true` if two bitboards intersect i.e. have at least one common
    /// set square.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let mut bb1 = Bitboard::from_iter([Square::E5, Square::D7]);
    /// let mut bb2 = Bitboard::from_iter([Square::A4, Square::B6, Square::E5]);
    /// assert!(bb1.intersects(bb2))
    /// ```
    #[inline]
    pub const fn intersects(&self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    /// Returns the intersection of two bitboards.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let mut bb1 = Bitboard::from_iter([Square::E5, Square::D7]);
    /// let mut bb2 = Bitboard::from_iter([Square::A4, Square::B6, Square::E5]);
    /// let intersection = bb1.intersection(bb2).into_iter().collect::<Vec<_>>();
    /// assert_eq!(intersection, vec![Square::E5])
    /// ```
    #[inline]
    pub const fn intersection(&self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// Returns the union of two bitboards.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let mut bb1 = Bitboard::from_iter([Square::E5, Square::D7]);
    /// let mut bb2 = Bitboard::from_iter([Square::A4, Square::B6, Square::E5]);
    /// let union = bb1.union(bb2).into_iter().collect::<Vec<_>>();
    /// assert_eq!(union, vec![Square::A4, Square::E5, Square::B6, Square::D7])
    /// ```
    #[inline]
    pub const fn union(&self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Shifts all squares of the bitboard in the given direction.
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// # use horsey::chess::square::*;
    /// let mut bb = Bitboard::from_iter([Square::E5, Square::D7]);
    /// let shifted_north = bb.shift(Delta::North).into_iter().collect::<Vec<_>>();
    /// assert_eq!(shifted_north, vec![Square::E6, Square::D8])
    /// ```
    #[inline]
    pub const fn shift(&self, delta: Delta) -> Self {
        Self(if 0 < delta as i8 {
            self.0 << (delta as u8)
        } else {
            self.0 >> (-(delta as i8) as u8)
        })
    }

    /// Inverts the bitboard (non-members of the set become members and vice-versa).
    /// # Example
    /// ```
    /// # use horsey::chess::bitboard::*;
    /// assert_eq!(Bitboard::universe().invert(), Bitboard::empty())
    /// ```
    #[inline]
    pub const fn invert(&self) -> Self {
        Self(!self.0)
    }

    /// Architecture independant PEXT (Parallel Bits Extract) implementation.
    ///
    /// Will be slower without the `bmi2` CPU flag.
    #[inline(always)]
    pub fn pext(self, mask: Self) -> Self {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            if is_x86_feature_detected!("bmi2") {
                return unsafe { self.pext_inner(mask) };
            }
        }
        let mut res = 0u64;
        let mut mask = mask.0;
        let mut bb = 1u64;
        while mask != 0 {
            if self.0 & mask & !mask != 0 {
                res |= bb
            }
            mask &= mask - 1;
            bb += bb
        }
        Bitboard(res)
    }

    /// Architecture independant PDEP (Parallel Bits Deposit) implementation.
    ///
    /// Will be slower without the `bmi2` CPU flag.
    #[inline(always)]
    pub fn pdep(self, mask: Self) -> Self {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            if is_x86_feature_detected!("bmi2") {
                return unsafe { self.pdep_inner(mask) };
            }
        }
        let mut res = 0u64;
        let mut mask = mask.0;
        let mut bb = 1u64;
        while mask != 0 {
            if self.0 & bb != 0 {
                res |= mask & !mask
            }
            mask &= mask - 1;
            bb += bb
        }
        Bitboard(res)
    }

    #[target_feature(enable = "bmi2")]
    unsafe fn pext_inner(self, mask: Self) -> Self {
        {
            use std::arch::x86_64::_pext_u64;

            Bitboard(unsafe { _pext_u64(self.0, mask.0) })
        }
    }

    #[target_feature(enable = "bmi2")]
    unsafe fn pdep_inner(self, mask: Self) -> Self {
        {
            use std::arch::x86_64::_pdep_u64;

            Bitboard(unsafe { _pdep_u64(self.0, mask.0) })
        }
    }

    /// Returns this bitboard as an array of bytes.
    ///
    /// Mainly used for FEN compression.
    #[inline]
    pub const fn as_bytes(self) -> [u8; 8] {
        self.0.to_be_bytes()
    }
}

// [BitAnd] implementations
impl std::ops::BitAnd for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        Bitboard(self.0 & rhs.0)
    }
}
impl std::ops::BitAnd for &Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitand(self, rhs: Self) -> Self::Output {
        Bitboard(self.0 & rhs.0)
    }
}
impl std::ops::BitAnd<&Bitboard> for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitand(self, rhs: &Self) -> Self::Output {
        Bitboard(self.0 & rhs.0)
    }
}
impl std::ops::BitAnd<Bitboard> for &Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitand(self, rhs: Bitboard) -> Self::Output {
        Bitboard(self.0 & rhs.0)
    }
}

impl std::ops::BitAndAssign for Bitboard {
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0
    }
}
impl std::ops::BitAndAssign<&Bitboard> for Bitboard {
    #[inline]
    fn bitand_assign(&mut self, rhs: &Bitboard) {
        self.0 &= rhs.0
    }
}

// [BitOr] implementations
impl std::ops::BitOr for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        Bitboard(self.0 | rhs.0)
    }
}
impl std::ops::BitOr for &Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitor(self, rhs: Self) -> Self::Output {
        Bitboard(self.0 | rhs.0)
    }
}
impl std::ops::BitOr<&Bitboard> for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitor(self, rhs: &Self) -> Self::Output {
        Bitboard(self.0 | rhs.0)
    }
}
impl std::ops::BitOr<Bitboard> for &Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitor(self, rhs: Bitboard) -> Self::Output {
        Bitboard(self.0 | rhs.0)
    }
}
impl std::ops::BitOrAssign for Bitboard {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0
    }
}
impl std::ops::BitOrAssign<&Bitboard> for Bitboard {
    #[inline]
    fn bitor_assign(&mut self, rhs: &Bitboard) {
        self.0 |= rhs.0
    }
}

// [BitXor] implementations
impl std::ops::BitXor for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        Bitboard(self.0 ^ rhs.0)
    }
}
impl std::ops::BitXor for &Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitxor(self, rhs: Self) -> Self::Output {
        Bitboard(self.0 ^ rhs.0)
    }
}
impl std::ops::BitXor<&Bitboard> for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitxor(self, rhs: &Self) -> Self::Output {
        Bitboard(self.0 ^ rhs.0)
    }
}
impl std::ops::BitXor<Bitboard> for &Bitboard {
    type Output = Bitboard;

    #[inline]
    fn bitxor(self, rhs: Bitboard) -> Self::Output {
        Bitboard(self.0 ^ rhs.0)
    }
}
impl std::ops::BitXorAssign for Bitboard {
    #[inline]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0
    }
}
impl std::ops::BitXorAssign<&Bitboard> for Bitboard {
    #[inline]
    fn bitxor_assign(&mut self, rhs: &Bitboard) {
        self.0 ^= rhs.0
    }
}

// [BitNot] implementations
impl std::ops::Not for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn not(self) -> Self::Output {
        Bitboard(!self.0)
    }
}
impl std::ops::Not for &Bitboard {
    type Output = Bitboard;

    #[inline]
    fn not(self) -> Self::Output {
        Bitboard(!self.0)
    }
}

// [Shl] implementations
impl std::ops::Shl<u8> for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn shl(self, rhs: u8) -> Self::Output {
        Bitboard(self.0 << rhs)
    }
}
impl std::ops::Shl<u8> for &Bitboard {
    type Output = Bitboard;

    #[inline]
    fn shl(self, rhs: u8) -> Self::Output {
        Bitboard(self.0 << rhs)
    }
}
impl std::ops::ShlAssign<u8> for Bitboard {
    #[inline]
    fn shl_assign(&mut self, rhs: u8) {
        self.0 <<= rhs
    }
}

// [Shr] implementations
impl std::ops::Shr<u8> for Bitboard {
    type Output = Bitboard;

    #[inline]
    fn shr(self, rhs: u8) -> Self::Output {
        Bitboard(self.0 >> rhs)
    }
}
impl std::ops::Shr<u8> for &Bitboard {
    type Output = Bitboard;

    #[inline]
    fn shr(self, rhs: u8) -> Self::Output {
        Bitboard(self.0 >> rhs)
    }
}
impl std::ops::ShrAssign<u8> for Bitboard {
    #[inline]
    fn shr_assign(&mut self, rhs: u8) {
        self.0 >>= rhs
    }
}

// [Add] implementations (shifts).
impl std::ops::Add<Delta> for Bitboard {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Delta) -> Self::Output {
        if 0 < rhs as i8 {
            self << (rhs as u8)
        } else {
            self >> (-(rhs as i8) as u8)
        }
    }
}
impl std::ops::AddAssign<Delta> for Bitboard {
    #[inline]
    fn add_assign(&mut self, rhs: Delta) {
        if 0 < rhs as i8 {
            *self <<= rhs as u8
        } else {
            *self >>= -(rhs as i8) as u8
        }
    }
}

// [Sub] implementations (reverse shifts).
impl std::ops::Sub<Delta> for Bitboard {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Delta) -> Self::Output {
        if 0 < rhs as i8 {
            self >> (rhs as u8)
        } else {
            self << (-(rhs as i8) as u8)
        }
    }
}
impl std::ops::SubAssign<Delta> for Bitboard {
    #[inline]
    fn sub_assign(&mut self, rhs: Delta) {
        if 0 < rhs as i8 {
            *self >>= rhs as u8
        } else {
            *self <<= -(rhs as i8) as u8
        }
    }
}

/// Iterates over set squares in a [Bitboard]
impl Iterator for Bitboard {
    type Item = Square;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.pop_lowest_square()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.len();
        (size as usize, Some(size as usize))
    }
}
/// Iterates over set squares top down.
impl DoubleEndedIterator for Bitboard {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.pop_highest_square()
    }
}
impl FusedIterator for Bitboard {}
impl ExactSizeIterator for Bitboard {
    #[inline]
    fn len(&self) -> usize {
        self.len() as usize
    }
}
impl FromIterator<Square> for Bitboard {
    fn from_iter<T: IntoIterator<Item = Square>>(iter: T) -> Self {
        let mut bb = Self::default();
        for sq in iter {
            bb.insert(sq);
        }
        bb
    }
}
impl Extend<Square> for Bitboard {
    fn extend<T: IntoIterator<Item = Square>>(&mut self, iter: T) {
        for sq in iter {
            self.insert(sq);
        }
    }
}

impl From<Bitboard> for u64 {
    fn from(value: Bitboard) -> Self {
        value.0
    }
}
impl From<&Bitboard> for u64 {
    fn from(value: &Bitboard) -> Self {
        value.0
    }
}
impl From<u64> for Bitboard {
    fn from(value: u64) -> Self {
        Self(value)
    }
}
impl From<&u64> for Bitboard {
    fn from(value: &u64) -> Self {
        Self(*value)
    }
}

impl std::fmt::Debug for Bitboard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:x}")
    }
}
impl std::fmt::Display for Bitboard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for rank in Rank::iter().rev() {
            for square in Square::rank_squares_iter(rank) {
                write!(f, "{} ", if self.is_set(square) { 'x' } else { '.' })?
            }
            writeln!(f)?
        }
        Ok(())
    }
}
impl std::fmt::UpperHex for Bitboard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:X}", self.0)
    }
}
impl std::fmt::LowerHex for Bitboard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:x}", self.0)
    }
}
impl std::fmt::Octal for Bitboard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:o}", self.0)
    }
}
impl std::fmt::Binary for Bitboard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:b}", self.0)
    }
}

#[cfg(test)]
mod test {
    use super::{super::square::Delta, Bitboard};

    #[test]
    fn shift_test() {
        let bb = Bitboard(0x1818000000);
        assert_eq!(bb + Delta::North, Bitboard(0x181800000000));
        assert_eq!(bb + Delta::South, Bitboard(0x18180000));
        assert_eq!(bb + Delta::East, Bitboard(0x3030000000));
        assert_eq!(bb + Delta::West, Bitboard(0xc0c000000));
        assert_eq!(bb + Delta::NorthEast, Bitboard(0x303000000000));
        assert_eq!(bb + Delta::NorthWest, Bitboard(0xc0c00000000));
        assert_eq!(bb + Delta::SouthEast, Bitboard(0x30300000));
        assert_eq!(bb + Delta::SouthWest, Bitboard(0xc0c0000));
    }

    #[test]
    fn neg_shift_test() {
        let bb = Bitboard(0x1818000000);
        assert_eq!(bb + Delta::North, bb - Delta::South);
        assert_eq!(bb + Delta::South, bb - Delta::North);
        assert_eq!(bb + Delta::East, bb - Delta::West);
        assert_eq!(bb + Delta::West, bb - Delta::East);
        assert_eq!(bb + Delta::NorthEast, bb - Delta::SouthWest);
        assert_eq!(bb + Delta::NorthWest, bb - Delta::SouthEast);
        assert_eq!(bb + Delta::SouthEast, bb - Delta::NorthWest);
        assert_eq!(bb + Delta::SouthWest, bb - Delta::NorthEast);
    }

    #[test]
    fn is_send() {
        fn assert_send<T: Send>() {}
        assert_send::<Bitboard>();
    }
    #[test]
    fn is_sync() {
        fn assert_sync<T: Send>() {}
        assert_sync::<Bitboard>();
    }
}
