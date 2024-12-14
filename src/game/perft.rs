//! # Perft testing/benchmarking

use std::time::Instant;

use super::position::Position;

/// Builder pattern to configure a Perft test.
pub struct PerftConfig {
    pub depth: u8,
    pub iterative: bool,
    pub bulk_counting: bool,
    pub divide: bool,

    pub bench: bool,

    pub show_board: bool,
}
impl PerftConfig {
    /// Whether to show the board and ascii art at the start of the program.
    ///
    /// Should be disabled when trying to parse the output.
    pub fn show_board(mut self, value: bool) -> Self {
        self.show_board = value;
        self
    }

    /// Sets the maximum depth of the perft run.
    pub fn with_depth(mut self, depth: u8) -> Self {
        self.depth = depth;
        self
    }

    /// If set to true, the run will start from all depth between 1 and the maximum.
    pub fn iterative_deepening(mut self, value: bool) -> Self {
        self.iterative = value;
        self
    }

    /// If set to true, simply returns the number of the legal moves at horizon nodes.
    pub fn bulk_counting(mut self, value: bool) -> Self {
        self.bulk_counting = value;
        self
    }

    /// Shows perft results per legal move at the starting position.
    pub fn divide_moves(mut self, value: bool) -> Self {
        self.divide = value;
        self
    }

    /// Measures the time it takes to complete one depth.
    pub fn benchmark(mut self, value: bool) -> Self {
        self.bench = value;
        self
    }

    /// Runs a Perft test on the given position.
    pub fn go(&self, position: &mut Position) {
        if self.show_board {
            println!(
                r"
                   __ _   
  _ __   ___ _ __ / _| |_ 
 | '_ \ / _ \ '__| |_| __|
 | |_) |  __/ |  |  _| |_ 
 | .__/ \___|_|  |_|  \__|
 |_|                      
"
            );
            println!("{position}");
        }

        if self.iterative && self.divide {
            println!("====== DEPTH 1 ======")
        }

        for depth in (if self.iterative { 1 } else { self.depth })..=self.depth {
            let start = Instant::now();
            let nodes: u64 = position
                .actions()
                .0
                .iter()
                .map(|&mv| {
                    position.make_legal(mv);
                    let mv_nodes = perft_rec(position, depth - 1, self.bulk_counting);
                    position.unmake();
                    if self.divide {
                        println!("{mv}: {mv_nodes} nodes");
                    }
                    mv_nodes
                })
                .sum();
            let elapsed = start.elapsed().as_secs_f64();
            println!("depth {depth}: {nodes} nodes");
            if self.bench {
                println!(
                    "\ttook {} ({})",
                    human_readable_time(elapsed),
                    human_readable_nps(nodes as f64 / elapsed)
                );
            }

            if self.iterative && self.divide && depth != self.depth {
                println!("\n====== DEPTH {} ======", depth + 1)
            }
        }
    }
}

/// Traverses all nodes accessible from a given position, returning the number of
/// nodes traversed.
fn perft_rec(position: &mut Position, depth_left: u8, bulk_counting: bool) -> u64 {
    if depth_left == 0 {
        1
    } else if depth_left == 1 && bulk_counting {
        position.actions().0.len() as u64
    } else {
        position
            .actions()
            .0
            .iter()
            .map(|&mv| {
                position.make_legal(mv);
                let mv_nodes = perft_rec(position, depth_left - 1, bulk_counting);
                position.unmake();
                mv_nodes
            })
            .sum()
    }
}

fn human_readable_time(secs: f64) -> String {
    if secs < 1. {
        format!("{:.3}ms", secs * 1_000.)
    } else if secs < 0.001 {
        format!("{:.3}μs", secs * 1_000_000.)
    } else if secs < 0.000_000_1 {
        format!("{:.3}ns", secs * 1_000_000_000.)
    } else {
        format!("{secs:.3}s")
    }
}

fn human_readable_nps(nps: f64) -> String {
    if nps > 1_000_000_000. {
        format!("{:.3}Gnps", nps / 1_000_000_000.)
    } else if nps > 1_000_000. {
        format!("{:.3}Mnps", nps / 1_000_000.)
    } else if nps > 1_000. {
        format!("{:.3}Knps", nps / 1_000.)
    } else {
        format!("{nps:.3}nps")
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn check_matching(position: &mut Position, expected: &[u64]) {
        for (depth, expected) in expected.into_iter().enumerate() {
            let actual = perft_rec(position, depth as u8 + 1, true);
            assert_eq!(
                actual,
                *expected,
                "Expected {expected} at depth {} for {}, but got {actual}",
                depth + 1,
                position.fen(),
            );
        }
    }

    #[test]
    #[ignore]
    fn initial_position_perft() {
        check_matching(
            &mut Position::initial(),
            &[20, 400, 8902, 197281, 4865609, 119060324, 3195901860],
        )
    }

    #[test]
    #[ignore]
    fn kiwipete_perft() {
        check_matching(
            &mut Position::from_fen(
                "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - ",
            )
            .unwrap(),
            &[48, 2039, 97862, 4085603, 193690690, 8031647685],
        )
    }

    #[test]
    #[ignore]
    fn endgame_perft() {
        check_matching(
            &mut Position::from_fen("8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - ").unwrap(),
            &[
                14, 191, 2812, 43238, 674624, 11030083, 178633661, 3009794393,
            ],
        )
    }

    #[test]
    #[ignore]
    fn mirrored_perft() {
        let expected = [6, 264, 9467, 422333, 15833292, 706045033];
        check_matching(
            &mut Position::from_fen(
                "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1",
            )
            .unwrap(),
            &expected,
        );
        check_matching(
            &mut Position::from_fen(
                "r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ - 0 1",
            )
            .unwrap(),
            &expected,
        )
    }

    #[test]
    #[ignore]
    fn buggy_perft() {
        check_matching(
            &mut Position::from_fen("rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8")
                .unwrap(),
            &[44, 1486, 62379, 2103487, 89941194],
        )
    }

    #[test]
    #[ignore]
    fn alternative_perft() {
        check_matching(
            &mut Position::from_fen(
                "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10",
            )
            .unwrap(),
            &[46, 2079, 89890, 3894594, 164075551, 6923051137],
        )
    }
}
