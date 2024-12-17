use super::{action::Action, castling_rights::CastlingRights, piece::PieceKind, square::File};

/// Records non-reversible informations that are lost when making a move.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct HistoryEntry {
    pub played: Action,
    pub captured: Option<PieceKind>,
    pub castling_rights: CastlingRights,
    pub reversible_moves: u8,
    pub en_passant_file: Option<File>,
    pub hash: u64,
}
