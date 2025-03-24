//! # Portable Game Notation standard implementation
//! The implementation follows the 2023-03-22 revision of the PGN standard which
//! can be found [here](https://github.com/fsmosca/PGN-Standard/blob/master/PGN-Standard.txt).

use super::action::SanMove;

/// Tags that may appear within a PGN database.
pub enum PgnTag {
    Event,
    Site,
    Date,
    Round,
    White,
    Black,
    Result,
    Other(String),
}

/// Tag pair representation for contextual game information.
pub struct TagPair {
    pub tag: PgnTag,
    pub value: String,
}

/// Represents a fully recorded PGN game, with contextual tags, moves played in order,
/// as well as annotations.
pub struct PgnGame {
    tags: Vec<TagPair>,
    moves: Vec<SanMove>,
    annotations: Vec<String>,
}
