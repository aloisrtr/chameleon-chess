//! # Utilities to handle scores in Chess (centipawns, win probability, ...)
pub type WinProbability = f32;
pub type CentiPawns = i32;

const CP_TO_WIN_PROB_CONST: WinProbability = 4.;
/// Converts a [`WinProbability`] into equivalent [`CentiPawns`] score.
/// # Example
/// ```
/// # use chameleon_chess::game::score::*;
/// assert_eq!(win_probability_to_centipawns(0.5), 0);
/// ```
pub fn win_probability_to_centipawns(probability: WinProbability) -> CentiPawns {
    (((1. - probability) / probability).log10() * CP_TO_WIN_PROB_CONST / 100.) as i32
}

/// Converts a [`CentiPawns`] score into equivalent [`WinProbability`].
/// # Example
/// ```
/// # use chameleon_chess::game::score::*;
/// assert_eq!(centipawns_to_win_probability(0), 0.5);
/// ```
pub fn centipawns_to_win_probability(cp: CentiPawns) -> WinProbability {
    1. / (1. + 10f32.powf(cp as f32 * 100. / CP_TO_WIN_PROB_CONST))
}
