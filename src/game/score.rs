//! # Utilities to handle different ways of scoring Chess positions (centipawns, win probability, etc).

/// Represents the probability of winning in the interval [0, 1], from the perspective
/// of white pieces. Values `< 0.5` indicate an advantage for black pieces, while
/// value `> 0.5` indicate an advantage for white pieces.
///
/// A value of 0.5 is given to positions considered neutral.
pub type WinProbability = f32;

/// Centipawn units advantage. Positive values indicates an advantage for white pieces,
/// while negative values indicate an advantage for black pieces.
///
/// A value of 0 is given to positions considered neutral.
pub type CentiPawns = i32;

const CP_TO_WIN_PROB_CONST: WinProbability = 4.;

/// Converts a [`WinProbability`] into equivalent [`CentiPawns`] score.
/// # Example
/// ```
/// # use horsey::game::score::*;
/// assert_eq!(win_probability_to_centipawns(0.5), 0);
/// ```
pub fn win_probability_to_centipawns(probability: WinProbability) -> CentiPawns {
    (((1. - probability) / probability).log10() * CP_TO_WIN_PROB_CONST / 100.) as i32
}

/// Converts a [`CentiPawns`] score into equivalent [`WinProbability`].
/// # Example
/// ```
/// # use horsey::game::score::*;
/// assert_eq!(centipawns_to_win_probability(0), 0.5);
/// ```
pub fn centipawns_to_win_probability(cp: CentiPawns) -> WinProbability {
    1. / (1. + 10f32.powf(cp as f32 * 100. / CP_TO_WIN_PROB_CONST))
}
