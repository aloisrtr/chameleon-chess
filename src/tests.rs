use crate::{
    position::{PieceKind, Position},
    square::{File, Rank, Square},
};

#[test]
fn initial_position_moves() {
    let position = Position::initial();
    println!("{position}");

    let moves = position.moves();
    for mv in moves {
        println!("{mv:?}")
    }
}

#[test]
fn npo_for_enums() {
    use std::mem::size_of;
    assert_eq!(size_of::<PieceKind>(), size_of::<Option<PieceKind>>());
    assert_eq!(size_of::<File>(), size_of::<Option<File>>());
    assert_eq!(size_of::<Rank>(), size_of::<Option<Rank>>());
    assert_eq!(size_of::<Square>(), size_of::<Option<Square>>());
}
