use crate::position::Position;

#[test]
fn initial_position_moves() {
    let position = Position::initial();
    println!("{position}");

    let moves = position.moves();
    for mv in moves {
        println!("{mv:?}")
    }
}
