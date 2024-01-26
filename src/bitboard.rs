//! Bitboards are an efficient way to represent sets of up to 64 elements,
//! and are used extensively in the board representation.

use std::{iter::FusedIterator, u8};

use crate::square::{Delta, Square};

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
/// Bitboards are data structures used to efficiently represent the board state.
///
/// They are augmented u64 values.
pub struct Bitboard(pub(crate) u64);
impl std::fmt::Debug for Bitboard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, square) in Square::squares_fen_iter().enumerate() {
            if i % 8 == 0 && i != 0 {
                writeln!(f)?
            }
            write!(f, "{} ", if self.is_set(square) { 'x' } else { '.' })?
        }
        Ok(())
    }
}
impl Bitboard {
    /// Returns an empty bitboard.
    #[inline(always)]
    pub const fn empty() -> Self {
        Self(0)
    }

    /// Returns the universal set (all bits to 1).
    #[inline(always)]
    pub const fn universal() -> Self {
        Self(u64::MAX)
    }

    /// Checks if a bitboard is empty.
    #[inline(always)]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Checks if a bitboard has one or more bits set.
    #[inline(always)]
    pub const fn is_not_empty(self) -> bool {
        self.0 != 0
    }

    /// Checks if a given square is set on the bitboard.
    #[inline(always)]
    pub const fn is_set(self, square: Square) -> bool {
        self.intersects(square.bitboard())
    }

    /// Checks if a bitboard has only one bit set.
    #[inline(always)]
    pub const fn is_single_populated(self) -> bool {
        self.0.is_power_of_two()
    }

    /// Checks if a bitboard has zero or one bits set.
    #[inline(always)]
    pub const fn has_at_most_one(self) -> bool {
        (self.0 & self.0.wrapping_sub(1)) == 0
    }

    /// Checks if a bitboard has more than one bit set.
    #[inline(always)]
    pub const fn has_more_than_one(self) -> bool {
        (self.0 & self.0.wrapping_sub(1)) != 0
    }

    /// Returns the cardinality of the bitboard (i.e. how many squares are set).
    #[inline(always)]
    pub const fn cardinality(self) -> u8 {
        self.0.count_ones() as u8
    }

    /// Returns the index of the LS1B in the bitboard.
    ///
    /// If the bitboard is empty, returns `None`.
    #[inline(always)]
    pub const fn lowest_set_square(self) -> Option<Square> {
        if !self.is_empty() {
            Some(unsafe { self.lowest_set_square_unchecked() })
        } else {
            None
        }
    }

    /// Returns the index of the LS1B in the bitboard.
    /// # Safety
    /// If passed an empty bitboard, the index will be 64 (out of bounds thus not usable).
    #[inline(always)]
    pub const unsafe fn lowest_set_square_unchecked(self) -> Square {
        Square::from_index_unchecked(self.0.trailing_zeros() as u8)
    }

    /// Pops the LS1B in the bitboard and returns its index.
    ///
    /// If the bitboard is empty, returns `None`.
    #[inline(always)]
    pub fn pop_lowest_set_square(&mut self) -> Option<Square> {
        if !Bitboard::is_empty(*self) {
            Some(unsafe { self.pop_lowest_set_square_unchecked() })
        } else {
            None
        }
    }

    /// Pops the LS1B in the bitboard and returns its index.
    /// # Safety
    /// If passed an empty bitboard, the returned index will be 64 (out of bounds thus not usable)
    #[inline(always)]
    pub unsafe fn pop_lowest_set_square_unchecked(&mut self) -> Square {
        let index = self.lowest_set_square_unchecked();
        self.0 &= self.0.wrapping_sub(1);
        index
    }

    /// Returns the index of the MS1B in the bitboard.
    ///
    /// If the bitboard is empty, returns `None`.
    #[inline(always)]
    pub const fn highest_set_square(self) -> Option<Square> {
        if !self.is_empty() {
            Some(unsafe { self.highest_set_square_unchecked() })
        } else {
            None
        }
    }

    /// Returns the index of the MS1B in the bitboard.
    /// # Safety
    /// If passed an empty bitboard, the index will be 64 (out of bounds thus not usable).
    #[inline(always)]
    pub const unsafe fn highest_set_square_unchecked(self) -> Square {
        Square::from_index_unchecked(self.0.leading_zeros() as u8)
    }

    /// Pops the MS1B in the bitboard and returns its index.
    ///
    /// If the bitboard is empty, returns `None`.
    #[inline(always)]
    pub fn pop_highest_set_square(&mut self) -> Option<Square> {
        if !Bitboard::is_empty(*self) {
            Some(unsafe { self.pop_highest_set_square_unchecked() })
        } else {
            None
        }
    }

    /// Pops the LS1B in the bitboard and returns its index.
    /// # Safety
    /// If passed an empty bitboard, the returned index will be 64 (out of bounds thus not usable)
    #[inline(always)]
    pub unsafe fn pop_highest_set_square_unchecked(&mut self) -> Square {
        let index = self.highest_set_square_unchecked();
        *self &= !index.bitboard();
        index
    }

    /// Returns true if two bitboards intersect i.e. have at least one common
    /// set square.
    #[inline(always)]
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    /// Returns the intersection of two bitboard.
    #[inline(always)]
    pub const fn intersection(self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// Applies shifts all bits of the bitboard in the given direction.
    #[inline(always)]
    pub const fn shift(self, delta: Delta) -> Self {
        Self(if 0 < delta as i8 {
            self.0 << (delta as u8)
        } else {
            self.0 >> (-(delta as i8) as u8)
        })
    }

    /// Inverts the bitboard.
    #[inline(always)]
    pub const fn invert(self) -> Self {
        Self(!self.0)
    }
}
impl std::ops::BitAnd for Bitboard {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        Self(self.0 & rhs.0)
    }
}
impl std::ops::BitAndAssign for Bitboard {
    #[inline(always)]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0
    }
}
impl std::ops::BitOr for Bitboard {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        Self(self.0 | rhs.0)
    }
}
impl std::ops::BitOrAssign for Bitboard {
    #[inline(always)]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0
    }
}
impl std::ops::BitXor for Bitboard {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self::Output {
        Self(self.0 ^ rhs.0)
    }
}
impl std::ops::BitXorAssign for Bitboard {
    #[inline(always)]
    fn bitxor_assign(&mut self, rhs: Self) {
        self.0 ^= rhs.0
    }
}
impl std::ops::Not for Bitboard {
    type Output = Self;

    #[inline(always)]
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

impl std::ops::Add<Delta> for Bitboard {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: Delta) -> Self::Output {
        Self(if 0 < rhs as i8 {
            self.0 << (rhs as u8)
        } else {
            self.0 >> (-(rhs as i8) as u8)
        })
    }
}
impl std::ops::AddAssign<Delta> for Bitboard {
    #[inline(always)]
    fn add_assign(&mut self, rhs: Delta) {
        if 0 < rhs as i8 {
            self.0 <<= rhs as u8
        } else {
            self.0 >>= -(rhs as i8) as u8
        }
    }
}
impl std::ops::Sub<Delta> for Bitboard {
    type Output = Self;

    #[inline(always)]
    fn sub(self, rhs: Delta) -> Self::Output {
        Self(if 0 < rhs as i8 {
            self.0 >> (rhs as u8)
        } else {
            self.0 << (-(rhs as i8) as u8)
        })
    }
}
impl std::ops::SubAssign<Delta> for Bitboard {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: Delta) {
        if 0 < rhs as i8 {
            self.0 >>= rhs as u8
        } else {
            self.0 <<= -(rhs as i8) as u8
        }
    }
}

impl Iterator for Bitboard {
    type Item = Square;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        self.pop_lowest_set_square()
    }

    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.cardinality();
        (size as usize, Some(size as usize))
    }
}
impl DoubleEndedIterator for Bitboard {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.pop_highest_set_square()
    }
}
impl FusedIterator for Bitboard {}
impl ExactSizeIterator for Bitboard {
    #[inline(always)]
    fn len(&self) -> usize {
        self.cardinality() as usize
    }
}

#[cfg(test)]
mod test {
    use crate::{bitboard::Bitboard, square::Delta};

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
}
