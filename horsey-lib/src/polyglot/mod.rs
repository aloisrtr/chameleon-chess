//! # PolyGlot opening book
//!
//! PolyGlot is a compact binary format for opening books, storing a sorted list of 16 byte
//! entries containing:
//! - a **key** to denote the position (which matches Zobrist hashing of a [`Position`])
//! - a **move**, its **quality** (how good the move is), and a mutable **learned value** field.
//!
//! Obtaining the binary data (from a file, network, peripheral, etc) is the responsibility
//! of the implementation. This module only provides a way to parse 16 byte slices
//! into a representation usable by the rest of this library, and turn said representation
//! back into 16 byte slices.

use crate::chess::{
    action::UciMove,
    piece::PromotionTarget,
    square::{File, Rank, Square},
};

/// Errors that may happen when reading a Polyglot entry from a slice of bytes.
pub enum PolyglotError {
    /// Only `n` bytes were available when 16 are needed.
    NotEnoughBytes(usize),
    /// The value of the `promotion_piece` field is invalid (more than 4)
    InvalidPromotion(u8),
}

/// A PolyGlot book entry, containing its key (hash of the corresponding [`Position`]),
/// move played, quality of the move and learned value.
///
/// While the semantics of the "quality" value are decided by book authors and are not
/// universal, the PolyGlot book generator interprets it as `2 * wins + draws`,
/// scaled to fit 16 bits if needed. Generally, it should be safe to assume that
/// a this value is proportional to how "good" the move is.
pub struct PolyglotEntry {
    pub key: u64,
    pub action: UciMove,
    pub quality: u16,
    pub learn: u32,
}
impl PolyglotEntry {
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, PolyglotError> {
        if bytes.len() < 16 {
            return Err(PolyglotError::NotEnoughBytes(bytes.len()));
        }

        let key = u64::from_be_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
        ]);
        let move_encoding = u16::from_be_bytes([bytes[8], bytes[9]]);
        let target_file_index = (move_encoding & 0b111) as u8;
        let target_rank_index = (move_encoding >> 3 & 0b111) as u8;
        let target_square = Square::new(
            File::from_index(target_file_index).unwrap(),
            Rank::from_index(target_rank_index).unwrap(),
        );
        let origin_file_index = (move_encoding >> 6 & 0b111) as u8;
        let origin_rank_index = (move_encoding >> 9 & 0b111) as u8;
        let origin_square = Square::new(
            File::from_index(origin_file_index).unwrap(),
            Rank::from_index(origin_rank_index).unwrap(),
        );
        let promotion_piece_index = (move_encoding >> 12 & 0b111) as u8;
        let promotion_piece = match promotion_piece_index {
            0 => None,
            1 => Some(PromotionTarget::Knight),
            2 => Some(PromotionTarget::Bishop),
            3 => Some(PromotionTarget::Rook),
            4 => Some(PromotionTarget::Queen),
            _ => return Err(PolyglotError::InvalidPromotion(promotion_piece_index)),
        };
        let uci_move = UciMove {
            origin: origin_square,
            target: target_square,
            promoting_to: promotion_piece,
        };

        let quality = u16::from_be_bytes([bytes[10], bytes[11]]);
        let learn = u32::from_be_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]);

        Ok(Self {
            key,
            action: uci_move,
            quality,
            learn,
        })
    }
}
impl TryFrom<&[u8]> for PolyglotEntry {
    type Error = PolyglotError;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        Self::from_bytes(value)
    }
}
