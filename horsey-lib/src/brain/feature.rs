//! # Feature set
//! This uses the HalfKP featureset. Each input indicates the position of our king,
//! occupied square, piece kind and colour.

use crate::chess::{colour::Colour, piece::PieceKind, position::Position, square::Square};

pub const FEATURES_COUNT: usize = 40960;

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct NnueFeatures {
    added_features: Vec<u16>,
    removed_features: Vec<u16>,
    should_refresh: bool,
}
impl Default for NnueFeatures {
    fn default() -> Self {
        Self {
            added_features: vec![],
            removed_features: vec![],
            should_refresh: true,
        }
    }
}
impl NnueFeatures {
    /// Creates a new [`Features`] structure.
    pub fn new() -> Self {
        Self::default()
    }

    /// Notes that these features should be refreshed.
    pub fn queue_refresh(&mut self) {
        self.should_refresh = true
    }

    /// Returns `true` if the NNUE accumulator should be refreshed.
    pub fn should_refresh(&self) -> bool {
        self.should_refresh
    }

    /// Clears accumulated NNUE features and refresh flag.
    pub fn clear_features(&mut self) {
        self.should_refresh = false;
        self.added_features.clear();
        self.removed_features.clear();
    }

    /// Returns a vector of active NNUE feature indices for this position.
    pub fn active_features(&self, position: &Position, perspective: Colour) -> Vec<u16> {
        let mut features = vec![];
        let king_square = position.king_square(perspective);

        for colour in [Colour::Black, Colour::White] {
            let colour_bb = position.color_bitboard(colour);
            for piece_kind in [
                PieceKind::Pawn,
                PieceKind::Knight,
                PieceKind::Bishop,
                PieceKind::Rook,
                PieceKind::Queen,
            ] {
                for piece_square in position.piece_bitboard(piece_kind) & colour_bb {
                    features.push(Self::feature_index(
                        king_square,
                        piece_square,
                        piece_kind,
                        colour,
                    ))
                }
            }
        }
        features
    }

    /// Returns accumulated added NNUE features.
    pub fn added_features(&self) -> &[u16] {
        &self.added_features
    }

    /// Returns accumulated removed NNUE features.
    pub fn removed_features(&self) -> &[u16] {
        &self.removed_features
    }

    #[inline(always)]
    pub fn add_piece_feature(&mut self, kind: PieceKind, square: Square, colour: Colour) {
        if self.should_refresh {
            return;
        }

        self.added_features
            .push(Self::piece_feature_index(square, kind, colour));
    }

    #[inline(always)]
    pub fn remove_piece_feature(&mut self, kind: PieceKind, square: Square, colour: Colour) {
        if self.should_refresh {
            return;
        }

        self.removed_features
            .push(Self::piece_feature_index(square, kind, colour))
    }

    /// Computes the index of a feature.
    #[inline(always)]
    const fn feature_index(
        king_square: Square,
        square: Square,
        kind: PieceKind,
        colour: Colour,
    ) -> u16 {
        (king_square as u16 * 640) + Self::piece_feature_index(square, kind, colour)
    }

    /// Computes the index of a piece feature, regardless of king position.
    #[inline(always)]
    const fn piece_feature_index(square: Square, kind: PieceKind, colour: Colour) -> u16 {
        (128 * kind as u16) + (64 * colour as u16) + square as u16
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn all_features_different() {
        let mut generated_by: [Option<(Square, Square, PieceKind, Colour)>; FEATURES_COUNT] =
            [None; FEATURES_COUNT];
        for king_square in Square::squares_iter() {
            for piece_square in Square::squares_iter() {
                for piece_kind in PieceKind::iter_all_but_king() {
                    for colour in [Colour::White, Colour::Black] {
                        let index = NnueFeatures::feature_index(
                            king_square,
                            piece_square,
                            piece_kind,
                            colour,
                        );
                        if index as usize >= FEATURES_COUNT {
                            panic!(
                                "({king_square}, {piece_square}, {piece_kind:?}, {colour:?}) has too big an index: {index}"
                            );
                        }
                        if let Some(set) = generated_by[index as usize] {
                            panic!(
                                "({king_square}, {piece_square}, {piece_kind:?}, {colour:?}) and ({}, {}, {:?}, {:?}) generated the same index: {index}",
                                set.0, set.1, set.2, set.3
                            )
                        }
                        generated_by[index as usize] =
                            Some((king_square, piece_square, piece_kind, colour))
                    }
                }
            }
        }
    }
}
