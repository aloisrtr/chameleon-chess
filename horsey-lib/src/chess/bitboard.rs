//! Bitboards are an efficient way to represent sets of up to 64 elements,
//! and are used extensively in the board representation.

use std::iter::FusedIterator;

use super::square::{Delta, Square};

/// Bitboards are data structures used to efficiently represent the board state.
///
/// They are augmented u64 values.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
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

    /// Returns the universal set (all bits to 1).
    #[inline]
    pub const fn universe() -> Self {
        Self::UNIVERSE
    }

    /// Checks if a bitboard is empty.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.0 == 0
    }

    /// Checks if a bitboard has one or more bits set.
    #[inline]
    pub const fn is_not_empty(&self) -> bool {
        self.0 != 0
    }

    /// Sets the square to occupied.
    #[inline]
    pub const fn set(&mut self, square: Square) {
        self.0 |= square.bitboard().0
    }

    /// Sets the square to empty.
    #[inline]
    pub const fn unset(&mut self, square: Square) {
        self.0 &= !square.bitboard().0
    }

    /// Toggles the occupancy of the square (if it was occupied it is now empty
    /// and vice-versa).
    #[inline]
    pub const fn toggle(&mut self, square: Square) {
        self.0 ^= square.bitboard().0
    }

    /// Checks if a given square is set on the bitboard.
    #[inline]
    pub const fn is_set(&self, square: Square) -> bool {
        self.intersects(square.bitboard())
    }

    /// Checks if a bitboard has only one bit set.
    #[inline]
    pub const fn is_single_populated(&self) -> bool {
        self.0.is_power_of_two()
    }

    /// Checks if a bitboard has zero or one bits set.
    #[inline]
    pub const fn has_at_most_one(&self) -> bool {
        (self.0 & self.0.wrapping_sub(1)) == 0
    }

    /// Checks if a bitboard has more than one bit set.
    #[inline]
    pub const fn has_more_than_one(&self) -> bool {
        (self.0 & self.0.wrapping_sub(1)) != 0
    }

    /// Returns the cardinality of the bitboard (i.e. how many squares are set).
    #[inline]
    pub const fn cardinality(&self) -> u8 {
        self.0.count_ones() as u8
    }

    /// Returns the index of the LS1B in the bitboard.
    ///
    /// If the bitboard is empty, returns `None`.
    #[inline]
    pub const fn lowest_set_square(&self) -> Option<Square> {
        if !self.is_empty() {
            Some(unsafe { self.lowest_set_square_unchecked() })
        } else {
            None
        }
    }

    /// Returns the index of the LS1B in the bitboard.
    ///
    /// # Safety
    /// If passed an empty bitboard, the index will be 64 (out of bounds thus not usable).
    #[inline]
    pub const unsafe fn lowest_set_square_unchecked(&self) -> Square {
        unsafe { Square::from_index_unchecked(self.0.trailing_zeros() as u8) }
    }

    /// Pops the LS1B in the bitboard and returns its index.
    ///
    /// If the bitboard is empty, returns `None`.
    #[inline]
    pub fn pop_lowest_set_square(&mut self) -> Option<Square> {
        if !Bitboard::is_empty(self) {
            Some(unsafe { self.pop_lowest_set_square_unchecked() })
        } else {
            None
        }
    }

    /// Pops the LS1B in the bitboard and returns its index.
    /// # Safety
    /// If passed an empty bitboard, the returned index will be 64 (out of bounds thus not usable)
    #[inline]
    pub unsafe fn pop_lowest_set_square_unchecked(&mut self) -> Square {
        let square = unsafe { self.lowest_set_square_unchecked() };
        self.0 &= self.0.wrapping_sub(1);
        square
    }

    /// Returns the index of the MS1B in the bitboard.
    ///
    /// If the bitboard is empty, returns `None`.
    #[inline]
    pub const fn highest_set_square(&self) -> Option<Square> {
        if !self.is_empty() {
            Some(unsafe { self.highest_set_square_unchecked() })
        } else {
            None
        }
    }

    /// Returns the index of the MS1B in the bitboard.
    /// # Safety
    /// If passed an empty bitboard, the index will be 64 (out of bounds thus not usable).
    #[inline]
    pub const unsafe fn highest_set_square_unchecked(&self) -> Square {
        unsafe { Square::from_index_unchecked(self.0.leading_zeros() as u8) }
    }

    /// Pops the MS1B in the bitboard and returns its index.
    ///
    /// If the bitboard is empty, returns `None`.
    #[inline]
    pub fn pop_highest_set_square(&mut self) -> Option<Square> {
        if !Bitboard::is_empty(self) {
            Some(unsafe { self.pop_highest_set_square_unchecked() })
        } else {
            None
        }
    }

    /// Pops the LS1B in the bitboard and returns its index.
    /// # Safety
    /// If passed an empty bitboard, the returned index will be 64 (out of bounds thus not usable)
    #[inline]
    pub unsafe fn pop_highest_set_square_unchecked(&mut self) -> Square {
        let square = unsafe { self.highest_set_square_unchecked() };
        *self ^= square.bitboard();
        square
    }

    /// Rotates the bitboard. This can be thought of as "looking at it from the
    /// opponent's perspective".
    #[inline]
    pub fn rotate(&self) -> Self {
        Self(self.0.swap_bytes())
    }

    /// Returns true if two bitboards intersect i.e. have at least one common
    /// set square.
    #[inline]
    pub const fn intersects(&self, other: Self) -> bool {
        self.0 & other.0 != 0
    }

    /// Returns the intersection of two bitboard.
    #[inline]
    pub const fn intersection(&self, other: Self) -> Self {
        Self(self.0 & other.0)
    }

    /// Applies shifts all bits of the bitboard in the given direction.
    #[inline]
    pub const fn shift(&self, delta: Delta) -> Self {
        Self(if 0 < delta as i8 {
            self.0 << (delta as u8)
        } else {
            self.0 >> (-(delta as i8) as u8)
        })
    }

    /// Inverts the bitboard.
    #[inline]
    pub const fn invert(&self) -> Self {
        Self(!self.0)
    }

    /// Architecture independant PEXT (Parallel Bits Extract) implementation.
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
    /// Will be slower without the `bmi2` CPU flag.
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
        self.pop_lowest_set_square()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.cardinality();
        (size as usize, Some(size as usize))
    }
}
/// Iterates over set squares top down.
impl DoubleEndedIterator for Bitboard {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.pop_highest_set_square()
    }
}
impl FusedIterator for Bitboard {}
impl ExactSizeIterator for Bitboard {
    #[inline]
    fn len(&self) -> usize {
        self.cardinality() as usize
    }
}

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
}
