use super::{action::LegalAction, piece::PieceKind, square::File};

/// Records non-reversible informations that are lost when making a move.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct HistoryEntry {
    pub played: LegalAction,
    pub captured: Option<PieceKind>,
    pub castling_rights: u8,
    pub reversible_moves: u8,
    pub en_passant_file: Option<File>,
    pub hash: u64,
}
