use crate::{position::PieceKind, square::Square};

///! A wrapper around moves that originates from a source that generates only
///! legal moves.
///!
///! These can be used in specific functions and are way faster to make on the board
///! since they bypass a lot of verifications.
#[derive(Clone, Copy, Hash, Eq, PartialEq, Debug)]
pub struct LegalMove(pub(crate) Move);
impl std::fmt::Display for LegalMove {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

///! Describes moves that can be played on a chessboard.
#[derive(Clone, Copy, Hash, Eq, PartialEq, Debug)]
pub struct Move {
    pub origin: Square,
    pub target: Square,
    pub kind: MoveKind,
}
impl std::fmt::Display for Move {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.origin, self.target)
    }
}

///! Types of castling moves.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub enum CastleKind {
    QueenSide,
    KingSide,
}
impl CastleKind {}

///! Exiting kinds of moves.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub enum MoveKind {
    Quiet,
    DoublePush,
    Castle(CastleKind),
    Capture,
    EnPassantCapture,
    Promotion(PieceKind),
    PromotionCapture(PieceKind),
}
