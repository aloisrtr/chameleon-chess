//! # Zobrist hashing keys and utilities

use std::sync::LazyLock;

use rand::{Rng, SeedableRng, rngs::SmallRng};

use super::{
    colour::Colour,
    piece::PieceKind,
    square::{File, Square},
};

pub static ZOBRIST_KEYS: LazyLock<[u64; 781]> = LazyLock::new(|| {
    let mut rng = SmallRng::seed_from_u64(0x6F2DF0EAF362C1ED);
    let mut keys = [0; 781];
    for key in &mut keys {
        *key = rng.random()
    }
    keys
});

// We need :
// - one number from piece on each square (64 * 12)
// - one number for side to move
// - four numbers for castling rights
// - eight numbers for en passant file
#[inline(always)]
pub fn piece_hash(kind: PieceKind, colour: Colour, square: Square) -> u64 {
    let piece_offset = kind as usize * square as usize;
    if colour.is_black() {
        ZOBRIST_KEYS[piece_offset + 64 * 6]
    } else {
        ZOBRIST_KEYS[piece_offset]
    }
}

pub const CASTLING_RIGHTS_OFFSET: usize = 64 * 12 + 1;

#[inline(always)]
pub fn side_to_move_hash() -> u64 {
    ZOBRIST_KEYS[64 * 12]
}
#[inline(always)]
pub fn en_passant_file_hash(file: File) -> u64 {
    ZOBRIST_KEYS[64 * 12 + 5 + file as usize]
}
