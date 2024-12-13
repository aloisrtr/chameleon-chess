//! # Zobrist hashing keys and utilities

use std::sync::LazyLock;

use rand::{thread_rng, Rng};

use super::{
    piece::PieceKind,
    square::{File, Square},
};

pub static ZOBRIST_KEYS: LazyLock<[u64; 781]> = LazyLock::new(|| {
    let mut keys = [0; 781];
    for key in &mut keys {
        *key = thread_rng().gen()
    }
    keys
});

// We need :
// - one number from piece on each square (64 * 12)
// - one number for side to move
// - four numbers for castling rights
// - eight numbers for en passant file

// We use overlapping keys to make it efficiently cachable.
// Accesses are byte aligned, making it so that we only need 784 bytes instead of
// 3124 bytes for aligned access.
#[inline(always)]
pub fn piece_hash<const BLACK_PIECE: bool>(kind: PieceKind, square: Square) -> u64 {
    let piece_offset = kind as usize * square as usize;
    if BLACK_PIECE {
        ZOBRIST_KEYS[piece_offset + 64 * 6]
    } else {
        ZOBRIST_KEYS[piece_offset]
    }
}
#[inline(always)]
pub fn side_to_move_hash() -> u64 {
    ZOBRIST_KEYS[64 * 12]
}
#[inline(always)]
pub fn queenside_right_hash<const BLACK: bool>() -> u64 {
    if BLACK {
        ZOBRIST_KEYS[64 * 12 + 4]
    } else {
        ZOBRIST_KEYS[64 * 12 + 2]
    }
}
#[inline(always)]
pub fn kingside_right_hash<const BLACK: bool>() -> u64 {
    if BLACK {
        ZOBRIST_KEYS[64 * 12 + 3]
    } else {
        ZOBRIST_KEYS[64 * 12 + 1]
    }
}
#[inline(always)]
pub fn en_passant_file_hash(file: File) -> u64 {
    ZOBRIST_KEYS[64 * 12 + 5 + file as usize]
}
