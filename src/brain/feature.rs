//! # Feature set
//! This uses the HalfKP featureset. Each input indicates the position of our king,
//! occupied square, piece kind and colour.

use crate::game::{colour::Colour, piece::PieceKind, square::Square};

pub const FEATURES_COUNT: usize = 40960;

/// Computes the index of a feature.
#[inline(always)]
pub const fn feature_index(
    king_square: Square,
    square: Square,
    kind: PieceKind,
    colour: Colour,
) -> u16 {
    (king_square as u16 * 640) + piece_feature_index(square, kind, colour)
}

/// Computes the index of a piece feature, regardless of king position.
#[inline(always)]
pub const fn piece_feature_index(square: Square, kind: PieceKind, colour: Colour) -> u16 {
    (128 * kind as u16) + (64 * colour as u16) + square as u16
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
                        let index = feature_index(king_square, piece_square, piece_kind, colour);
                        if index as usize >= FEATURES_COUNT {
                            panic!("({king_square}, {piece_square}, {piece_kind:?}, {colour:?}) has too big an index: {index}");
                        }
                        if let Some(set) = generated_by[index as usize] {
                            panic!("({king_square}, {piece_square}, {piece_kind:?}, {colour:?}) and ({}, {}, {:?}, {:?}) generated the same index: {index}", set.0, set.1, set.2, set.3)
                        }
                        generated_by[index as usize] =
                            Some((king_square, piece_square, piece_kind, colour))
                    }
                }
            }
        }
    }
}
