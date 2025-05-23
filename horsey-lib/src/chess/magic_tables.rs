//! Lookup tables for stuff like magic bitboards, knight moves, etc
use std::mem::MaybeUninit;

use super::{
    bitboard::Bitboard,
    square::{Delta, File, Square},
};

/// Returns knight moves from an origin square.
#[inline(always)]
pub fn knight_moves(origin: Square) -> Bitboard {
    unsafe { *KNIGHT_MOVES.get_unchecked(origin as usize) }
}

/// Returns king moves from an origin square.
#[inline(always)]
pub fn king_moves(origin: Square) -> Bitboard {
    unsafe { *KING_MOVES.get_unchecked(origin as usize) }
}

/// Returns diagonal slider moves from an origin square and given blockers.
#[inline(always)]
pub fn diagonal_moves(origin: Square, blockers: Bitboard) -> Bitboard {
    unsafe {
        SLIDERS_TABLE_ENTRIES
            .get_unchecked(origin as usize)
            .get(blockers)
    }
}
/// Returns orthogonal slider moves from an origin square and given blockers.
#[inline(always)]
pub fn orthogonal_moves(origin: Square, blockers: Bitboard) -> Bitboard {
    unsafe {
        SLIDERS_TABLE_ENTRIES
            .get_unchecked(origin as usize + 64)
            .get(blockers)
    }
}

/// Lookup for king moves from a given square.
static KING_MOVES: [Bitboard; 64] = {
    let mut result = [Bitboard::empty(); 64];
    let mut origin = 0;
    let west = File::A.bitboard().invert();
    let east = File::H.bitboard().invert();
    while origin < 64 {
        let origin_bb = Bitboard(1 << origin);
        result[origin as usize].0 |= origin_bb.intersection(west).shift(Delta::West).0
            | origin_bb.intersection(east).shift(Delta::East).0
            | origin_bb.shift(Delta::North).0
            | origin_bb.shift(Delta::South).0
            | origin_bb.intersection(east).shift(Delta::NorthEast).0
            | origin_bb.intersection(east).shift(Delta::SouthEast).0
            | origin_bb.intersection(west).shift(Delta::NorthWest).0
            | origin_bb.intersection(west).shift(Delta::SouthWest).0;

        origin += 1;
    }
    result
};

/// Lookup for knight moves from a given square.
static KNIGHT_MOVES: [Bitboard; 64] = {
    let mut result = [Bitboard::empty(); 64];
    let mut origin = 0;
    let west = File::A.bitboard().invert();
    let east = File::H.bitboard().invert();
    let two_west = File::A
        .bitboard()
        .invert()
        .intersection(File::B.bitboard().invert());
    let two_east = File::H
        .bitboard()
        .invert()
        .intersection(File::G.bitboard().invert());
    while origin < 64 {
        let origin_bb = Bitboard(1 << origin);
        result[origin as usize].0 |= origin_bb.intersection(east).shift(Delta::KnightNorthEast).0
            | origin_bb.intersection(west).shift(Delta::KnightNorthWest).0
            | origin_bb.intersection(east).shift(Delta::KnightSouthEast).0
            | origin_bb.intersection(west).shift(Delta::KnightSouthWest).0
            | origin_bb
                .intersection(two_east)
                .shift(Delta::KnightEastNorth)
                .0
            | origin_bb
                .intersection(two_west)
                .shift(Delta::KnightWestNorth)
                .0
            | origin_bb
                .intersection(two_east)
                .shift(Delta::KnightEastSouth)
                .0
            | origin_bb
                .intersection(two_west)
                .shift(Delta::KnightWestSouth)
                .0;

        origin += 1;
    }
    result
};

/// An entry in the sliders' move lookup table.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct SliderTableEntry {
    magic: u64,
    blockers_mask: Bitboard,
    shift: u8,
    table: *const Bitboard,
}
impl SliderTableEntry {
    /// Given a set of blockers, returns the corresponding bitboard of reachable
    /// squares from the slider table.
    #[inline(always)]
    pub fn get(self, blockers: Bitboard) -> Bitboard {
        unsafe {
            self.table
                .add(
                    ((blockers.0 & self.blockers_mask.0).wrapping_mul(self.magic) >> self.shift)
                        as usize,
                )
                .read()
        }
    }
}
unsafe impl Send for SliderTableEntry {}
unsafe impl Sync for SliderTableEntry {}

static SLIDERS_TABLE_ENTRIES: [SliderTableEntry; 128] = {
    let magics: [u64; 128] = [
        293861533946085504,
        99361787782299656,
        22525712988637184,
        4613984015446213888,
        5068817994614090,
        2594359289528517184,
        106721483702305,
        81205810356633664,
        144119792358458368,
        11872053775349449216,
        13835075664652451840,
        5513685797012766784,
        2305847463640276992,
        42784772266663942,
        1153203565914767872,
        297273035764830208,
        5242226387951288624,
        797137143439885064,
        1157425108546093072,
        2324983410830872576,
        19144705070333954,
        9241562365849242112,
        1234273289829892616,
        77405623762879504,
        2310645693859631104,
        82226501491623040,
        1129267195281664,
        4648286562633666592,
        288375512231845904,
        13511906992079130,
        9692872916553040128,
        576534421785085957,
        5766863996057815300,
        112735267954098752,
        4760516118593409088,
        36592299429462528,
        577587751990591552,
        652177817391465232,
        3395850386800896,
        4614089689358532864,
        943697653966118912,
        9656847917364814336,
        10700844361299529728,
        1152921780294320640,
        1225832388660102144,
        9225907613781336128,
        49698587008839744,
        13671329744027680,
        651056638528127296,
        2816955334008835,
        2262804627720256,
        2305984898861761024,
        1176854726913,
        144150389896282368,
        2254067623727488,
        4543217220069376,
        578220254453325888,
        1300415494196822656,
        159968119631228928,
        11269994189029888,
        136381706,
        180665516544,
        576496623937978432,
        4616207218964971536,
        4647715090332655792,
        1459167654462906369,
        144125633753120832,
        2954366862241038424,
        1297063219743031300,
        72059814541525000,
        1224988994410127872,
        36036493603553664,
        6918232732809576448,
        4611827030802063360,
        9228157184475399360,
        288371182367934464,
        1153203055097825280,
        72198614994387072,
        8072983953071673600,
        18155284174225664,
        18023744383633832,
        40532671593448016,
        4683815081258012930,
        612518137700553216,
        1167576895161106688,
        292875264130569216,
        4614232487500972802,
        74386359732707393,
        180495830965321728,
        9007337767522304,
        5069306951122976,
        1153203018239312096,
        9223447907454681296,
        2306405967757349128,
        18093580529697538,
        4611826895502459136,
        27162353590083840,
        35195252129793,
        729587816870187040,
        4504149727119360,
        578714201527157760,
        432908548574284816,
        2312616172706611713,
        9241527191785701632,
        13835199067751219201,
        1170936180158824481,
        1152939097329795200,
        563224968036368,
        297801281811382280,
        144181158807109760,
        281500746579972,
        36873291884986370,
        563449318932992,
        1153062379555127680,
        2394805046872192,
        4620836738310340736,
        145522718786261248,
        360448498954436736,
        20973229532251136,
        2449963974097895936,
        71473121210498,
        2392952185831425,
        9232389142764060737,
        9226186855879034946,
        1188959098013810693,
        613334010797752337,
        72339077604839557,
        2333991061002658114,
    ];
    let blockers: [u64; 128] = [
        18049651735527936,
        70506452091904,
        275415828992,
        1075975168,
        38021120,
        8657588224,
        2216338399232,
        567382630219776,
        9024825867763712,
        18049651735527424,
        70506452221952,
        275449643008,
        9733406720,
        2216342585344,
        567382630203392,
        1134765260406784,
        4512412933816832,
        9024825867633664,
        18049651768822272,
        70515108615168,
        2491752130560,
        567383701868544,
        1134765256220672,
        2269530512441344,
        2256206450263040,
        4512412900526080,
        9024834391117824,
        18051867805491712,
        637888545440768,
        1135039602493440,
        2269529440784384,
        4539058881568768,
        1128098963916800,
        2256197927833600,
        4514594912477184,
        9592139778506752,
        19184279556981248,
        2339762086609920,
        4538784537380864,
        9077569074761728,
        562958610993152,
        1125917221986304,
        2814792987328512,
        5629586008178688,
        11259172008099840,
        22518341868716544,
        9007336962655232,
        18014673925310464,
        2216338399232,
        4432676798464,
        11064376819712,
        22137335185408,
        44272556441600,
        87995357200384,
        35253226045952,
        70506452091904,
        567382630219776,
        1134765260406784,
        2832480465846272,
        5667157807464448,
        11333774449049600,
        22526811443298304,
        9024825867763712,
        18049651735527936,
        282578800148862,
        565157600297596,
        1130315200595066,
        2260630401190006,
        4521260802379886,
        9042521604759646,
        18085043209519166,
        36170086419038334,
        282578800180736,
        565157600328704,
        1130315200625152,
        2260630401218048,
        4521260802403840,
        9042521604775424,
        18085043209518592,
        36170086419037696,
        282578808340736,
        565157608292864,
        1130315208328192,
        2260630408398848,
        4521260808540160,
        9042521608822784,
        18085043209388032,
        36170086418907136,
        282580897300736,
        565159647117824,
        1130317180306432,
        2260632246683648,
        4521262379438080,
        9042522644946944,
        18085043175964672,
        36170086385483776,
        283115671060736,
        565681586307584,
        1130822006735872,
        2261102847592448,
        4521664529305600,
        9042787892731904,
        18085034619584512,
        36170077829103616,
        420017753620736,
        699298018886144,
        1260057572672512,
        2381576680245248,
        4624614895390720,
        9110691325681664,
        18082844186263552,
        36167887395782656,
        35466950888980736,
        34905104758997504,
        34344362452452352,
        33222877839362048,
        30979908613181440,
        26493970160820224,
        17522093256097792,
        35607136465616896,
        9079539427579068672,
        8935706818303361536,
        8792156787827803136,
        8505056726876686336,
        7930856604974452736,
        6782456361169985536,
        4485655873561051136,
        9115426935197958144,
    ];

    let mut entries: [MaybeUninit<SliderTableEntry>; 128] =
        unsafe { MaybeUninit::uninit().assume_init() };

    let mut square = 0;
    let mut table = SLIDERS_TABLE.as_ptr();
    while square < 128 {
        let bits = blockers[square].count_ones() as u8;
        let entry = SliderTableEntry {
            magic: magics[square],
            blockers_mask: Bitboard(blockers[square]),
            shift: 64 - bits,
            table,
        };
        entries[square] = MaybeUninit::new(entry);
        unsafe { table = table.add(1 << (bits as usize)) }

        square += 1;
    }
    unsafe { std::mem::transmute(entries) }
};

/// This constant is computed ASSUMING THAT SLIDER_TABLE_ENTRIES IS CORRECT.
/// If this assumption doesn't hold, the program is entirely incorrect.
static SLIDERS_TABLE: [Bitboard; 107648] = {
    let magics: [u64; 128] = [
        293861533946085504,
        99361787782299656,
        22525712988637184,
        4613984015446213888,
        5068817994614090,
        2594359289528517184,
        106721483702305,
        81205810356633664,
        144119792358458368,
        11872053775349449216,
        13835075664652451840,
        5513685797012766784,
        2305847463640276992,
        42784772266663942,
        1153203565914767872,
        297273035764830208,
        5242226387951288624,
        797137143439885064,
        1157425108546093072,
        2324983410830872576,
        19144705070333954,
        9241562365849242112,
        1234273289829892616,
        77405623762879504,
        2310645693859631104,
        82226501491623040,
        1129267195281664,
        4648286562633666592,
        288375512231845904,
        13511906992079130,
        9692872916553040128,
        576534421785085957,
        5766863996057815300,
        112735267954098752,
        4760516118593409088,
        36592299429462528,
        577587751990591552,
        652177817391465232,
        3395850386800896,
        4614089689358532864,
        943697653966118912,
        9656847917364814336,
        10700844361299529728,
        1152921780294320640,
        1225832388660102144,
        9225907613781336128,
        49698587008839744,
        13671329744027680,
        651056638528127296,
        2816955334008835,
        2262804627720256,
        2305984898861761024,
        1176854726913,
        144150389896282368,
        2254067623727488,
        4543217220069376,
        578220254453325888,
        1300415494196822656,
        159968119631228928,
        11269994189029888,
        136381706,
        180665516544,
        576496623937978432,
        4616207218964971536,
        4647715090332655792,
        1459167654462906369,
        144125633753120832,
        2954366862241038424,
        1297063219743031300,
        72059814541525000,
        1224988994410127872,
        36036493603553664,
        6918232732809576448,
        4611827030802063360,
        9228157184475399360,
        288371182367934464,
        1153203055097825280,
        72198614994387072,
        8072983953071673600,
        18155284174225664,
        18023744383633832,
        40532671593448016,
        4683815081258012930,
        612518137700553216,
        1167576895161106688,
        292875264130569216,
        4614232487500972802,
        74386359732707393,
        180495830965321728,
        9007337767522304,
        5069306951122976,
        1153203018239312096,
        9223447907454681296,
        2306405967757349128,
        18093580529697538,
        4611826895502459136,
        27162353590083840,
        35195252129793,
        729587816870187040,
        4504149727119360,
        578714201527157760,
        432908548574284816,
        2312616172706611713,
        9241527191785701632,
        13835199067751219201,
        1170936180158824481,
        1152939097329795200,
        563224968036368,
        297801281811382280,
        144181158807109760,
        281500746579972,
        36873291884986370,
        563449318932992,
        1153062379555127680,
        2394805046872192,
        4620836738310340736,
        145522718786261248,
        360448498954436736,
        20973229532251136,
        2449963974097895936,
        71473121210498,
        2392952185831425,
        9232389142764060737,
        9226186855879034946,
        1188959098013810693,
        613334010797752337,
        72339077604839557,
        2333991061002658114,
    ];
    let blockers: [u64; 128] = [
        18049651735527936,
        70506452091904,
        275415828992,
        1075975168,
        38021120,
        8657588224,
        2216338399232,
        567382630219776,
        9024825867763712,
        18049651735527424,
        70506452221952,
        275449643008,
        9733406720,
        2216342585344,
        567382630203392,
        1134765260406784,
        4512412933816832,
        9024825867633664,
        18049651768822272,
        70515108615168,
        2491752130560,
        567383701868544,
        1134765256220672,
        2269530512441344,
        2256206450263040,
        4512412900526080,
        9024834391117824,
        18051867805491712,
        637888545440768,
        1135039602493440,
        2269529440784384,
        4539058881568768,
        1128098963916800,
        2256197927833600,
        4514594912477184,
        9592139778506752,
        19184279556981248,
        2339762086609920,
        4538784537380864,
        9077569074761728,
        562958610993152,
        1125917221986304,
        2814792987328512,
        5629586008178688,
        11259172008099840,
        22518341868716544,
        9007336962655232,
        18014673925310464,
        2216338399232,
        4432676798464,
        11064376819712,
        22137335185408,
        44272556441600,
        87995357200384,
        35253226045952,
        70506452091904,
        567382630219776,
        1134765260406784,
        2832480465846272,
        5667157807464448,
        11333774449049600,
        22526811443298304,
        9024825867763712,
        18049651735527936,
        282578800148862,
        565157600297596,
        1130315200595066,
        2260630401190006,
        4521260802379886,
        9042521604759646,
        18085043209519166,
        36170086419038334,
        282578800180736,
        565157600328704,
        1130315200625152,
        2260630401218048,
        4521260802403840,
        9042521604775424,
        18085043209518592,
        36170086419037696,
        282578808340736,
        565157608292864,
        1130315208328192,
        2260630408398848,
        4521260808540160,
        9042521608822784,
        18085043209388032,
        36170086418907136,
        282580897300736,
        565159647117824,
        1130317180306432,
        2260632246683648,
        4521262379438080,
        9042522644946944,
        18085043175964672,
        36170086385483776,
        283115671060736,
        565681586307584,
        1130822006735872,
        2261102847592448,
        4521664529305600,
        9042787892731904,
        18085034619584512,
        36170077829103616,
        420017753620736,
        699298018886144,
        1260057572672512,
        2381576680245248,
        4624614895390720,
        9110691325681664,
        18082844186263552,
        36167887395782656,
        35466950888980736,
        34905104758997504,
        34344362452452352,
        33222877839362048,
        30979908613181440,
        26493970160820224,
        17522093256097792,
        35607136465616896,
        9079539427579068672,
        8935706818303361536,
        8792156787827803136,
        8505056726876686336,
        7930856604974452736,
        6782456361169985536,
        4485655873561051136,
        9115426935197958144,
    ];
    let mut table: [Bitboard; 107648] = [Bitboard::empty(); 107648];

    let mut square = 0;
    let mut offset = 0;
    while square < 128 {
        let origin = unsafe { Square::from_index_unchecked(square as u8 % 64) };
        let bits = blockers[square].count_ones() as u8;
        let shift = 64 - bits;

        let mut current_blockers = Bitboard::empty();
        loop {
            let index = ((current_blockers.0 & blockers[square]).wrapping_mul(magics[square])
                >> shift) as usize;

            // Generate moves
            if table[offset + index].is_empty() {
                table[offset + index] = if square < 64 {
                    diagonal_attacks(origin, current_blockers)
                } else {
                    orthogonal_attacks(origin, current_blockers)
                }
            }

            current_blockers.0 =
                current_blockers.0.wrapping_sub(blockers[square]) & blockers[square];
            if current_blockers.is_empty() {
                break;
            }
        }

        offset += 1 << bits;
        square += 1;
    }

    table
};

// Kogge-Stone algorithm for fast sliding piece moves.
const fn orthogonal_attacks(origin: Square, blockers: Bitboard) -> Bitboard {
    let bb = origin.bitboard().0;
    let empty = !blockers.0;
    Bitboard(
        south_ray(bb, empty) | north_ray(bb, empty) | east_ray(bb, empty) | west_ray(bb, empty),
    )
}
const fn diagonal_attacks(origin: Square, blockers: Bitboard) -> Bitboard {
    let bb = origin.bitboard().0;
    let empty = !blockers.0;
    Bitboard(
        south_east_ray(bb, empty)
            | north_west_ray(bb, empty)
            | north_east_ray(bb, empty)
            | south_west_ray(bb, empty),
    )
}
const fn south_ray(mut filled: u64, mut empty: u64) -> u64 {
    filled |= empty & (filled >> 8);
    empty &= empty >> 8;
    filled |= empty & (filled >> 16);
    empty &= empty >> 16;
    filled |= empty & (filled >> 32);
    filled >> 8
}
const fn north_ray(mut filled: u64, mut empty: u64) -> u64 {
    filled |= empty & (filled << 8);
    empty &= empty << 8;
    filled |= empty & (filled << 16);
    empty &= empty << 16;
    filled |= empty & (filled << 32);
    filled << 8
}
const fn east_ray(mut filled: u64, mut empty: u64) -> u64 {
    empty &= !File::A.bitboard().0;
    filled |= empty & (filled << 1);
    empty &= empty << 1;
    filled |= empty & (filled << 2);
    empty &= empty << 2;
    filled |= empty & (filled << 4);
    (filled << 1) & !File::A.bitboard().0
}
const fn north_east_ray(mut filled: u64, mut empty: u64) -> u64 {
    empty &= !File::A.bitboard().0;
    filled |= empty & (filled << 9);
    empty &= empty << 9;
    filled |= empty & (filled << 18);
    empty &= empty << 18;
    filled |= empty & (filled << 36);
    (filled << 9) & !File::A.bitboard().0
}
const fn south_east_ray(mut filled: u64, mut empty: u64) -> u64 {
    empty &= !File::A.bitboard().0;
    filled |= empty & (filled >> 7);
    empty &= empty >> 7;
    filled |= empty & (filled >> 14);
    empty &= empty >> 14;
    filled |= empty & (filled >> 28);
    (filled >> 7) & !File::A.bitboard().0
}
const fn west_ray(mut filled: u64, mut empty: u64) -> u64 {
    empty &= !File::H.bitboard().0;
    filled |= empty & (filled >> 1);
    empty &= empty >> 1;
    filled |= empty & (filled >> 2);
    empty &= empty >> 2;
    filled |= empty & (filled >> 4);
    (filled >> 1) & !File::H.bitboard().0
}
const fn north_west_ray(mut filled: u64, mut empty: u64) -> u64 {
    empty &= !File::H.bitboard().0;
    filled |= empty & (filled << 7);
    empty &= empty << 7;
    filled |= empty & (filled << 14);
    empty &= empty << 14;
    filled |= empty & (filled << 28);
    (filled << 7) & !File::H.bitboard().0
}
const fn south_west_ray(mut filled: u64, mut empty: u64) -> u64 {
    empty &= !File::H.bitboard().0;
    filled |= empty & (filled >> 9);
    empty &= empty >> 9;
    filled |= empty & (filled >> 18);
    empty &= empty >> 18;
    filled |= empty & (filled >> 36);
    (filled >> 9) & !File::H.bitboard().0
}
