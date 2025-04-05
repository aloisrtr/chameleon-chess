//! # Numeric Annotation Glyph description
//! An enum associating all NAG values defined in the PGN standard with their
//! general meaning.
//!
//! This can be used instead of raw integers for more human-readable/self-documenting
//! code.

use crate::chess::{colour::Colour, piece::PromotionTarget};

#[repr(u8)]
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum NumericAnnotationGlyph {
    Null,
    GoodMove,
    PoorMove,
    BrilliantMove,
    Blunder,
    SpeculativeMove,
    DubiousMove,
    ForcedMove,
    OnlyMove,
    WorstMove,
    DrawishPosition,
    EqualChancesQuiet,
    EqualChancesActive,
    UnclearPosition,
    SlightAdvantage(Colour),
    ModerateAdvantage(Colour),
    DecisiveAdvantage(Colour),
    CrushingAdvantage(Colour),
    Zugzwang(Colour),
    SlightSpaceAdvantage(Colour),
    ModerateSpaceAdvantage(Colour),
    DecisiveSpaceAdvantage(Colour),
    SlightDevelopmentAdvantage(Colour),
    ModerateDevelopmentAdvantage(Colour),
    DecisiveDevelopmentAdvantage(Colour),
    Initiative(Colour),
    LastingInitiative(Colour),
    Attacking(Colour),
    InsufficientCompensation(Colour),
    SufficientCompensation(Colour),
    MoreThanAdequateCompensation(Colour),
    SlightCenterControlAdvantage(Colour),
    ModerateCenterControlAdvantage(Colour),
    DecisiveCenterControlAdvantage(Colour),
    SlightKingsideControlAdvantage(Colour),
    ModerateKingsideControlAdvantage(Colour),
    DecisiveKingsideControlAdvantage(Colour),
    SlightQueensideControlAdvantage(Colour),
    ModerateQueensideControlAdvantage(Colour),
    DecisiveQueensideControlAdvantage(Colour),
    VulnerableFirstRank(Colour),
    WellProtectedFirstRank(Colour),
    VulnerableKing(Colour),
    WellProtectedKing(Colour),
    PoorlyPlacedKing(Colour),
    WellPlacedKing(Colour),
    VeryWeakPawnStructure(Colour),
    ModeratelyWeakPawnStructure(Colour),
    ModeratelyStrongPawnStructure(Colour),
    VeryStrongPawnStructure(Colour),
    PoorPiecePlacement(Colour, PromotionTarget),
    GoodPiecePlacement(Colour, PromotionTarget),
    PoorPieceCoordination(Colour),
    GoodPieceCoordination(Colour),
    VeryPoorOpening(Colour),
    PoorOpening(Colour),
    GoodOpening(Colour),
    VeryGoodOpening(Colour),
    VeryPoorMidgame(Colour),
    PoorMidgame(Colour),
    GoodMidgame(Colour),
    VeryGoodMidgame(Colour),
    VeryPoorEndgame(Colour),
    PoorEndgame(Colour),
    GoodEndgame(Colour),
    VeryGoodEndgame(Colour),
    SlightCounterPlay(Colour),
    ModerateCounterPlay(Colour),
    DecisiveCounterPlay(Colour),
    ModerateTimeControlPressure(Colour),
    SevereTimeControlPressure(Colour),
}
impl From<u8> for NumericAnnotationGlyph {
    fn from(value: u8) -> Self {
        use NumericAnnotationGlyph::*;
        match value {
            0 => Null,
            1 => GoodMove,
            2 => PoorMove,
            3 => BrilliantMove,
            4 => Blunder,
            5 => SpeculativeMove,
            6 => DubiousMove,
            7 => ForcedMove,
            8 => OnlyMove,
            9 => WorstMove,
            10 => DrawishPosition,
            11 => EqualChancesQuiet,
            12 => EqualChancesActive,
        }
    }
}

impl From<NumericAnnotationGlyph> for u8 {
    fn from(value: NumericAnnotationGlyph) -> Self {}
}
