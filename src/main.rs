use std::path::PathBuf;

use clap::{Parser, Subcommand};
#[cfg(feature = "perft")]
use horsey::game::perft::PerftConfig;
#[cfg(feature = "train")]
use horsey::{brain::training::selfplay, search::SearchConfig};
use horsey::{game::position::Position, uci::uci_client};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Arguments {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand, Debug)]
enum Command {
    /// Runs the engine in UCI mode (DEFAULT)
    Uci,
    /// Runs perft (generating all moves up to a certain depth)
    Perft {
        /// Maximum depth to reach
        depth: u8,
        /// Starting position as a FEN string.
        #[arg(short, long)]
        position: Option<String>,
        /// Shows move count for each move from the starting position
        #[arg(short)]
        divide: bool,
        /// Generates moves for each depth up to the maximum
        #[arg(short)]
        iterative: bool,
        /// Show timing information
        #[arg(long)]
        bench: bool,
        /// Counts legal moves at horizon nodes instead of playing each of them
        #[arg(short)]
        bulk: bool,

        /// Does not show the board and other decorations
        #[arg(long)]
        no_board: bool,
    },
    /// Generates a batch of selfplay games
    SelfPlay { games: usize, output: PathBuf },
}

pub fn main() {
    let args = Arguments::parse();
    env_logger::init();

    match args.command.unwrap_or(Command::Uci) {
        Command::Uci => uci_client().unwrap(),
        #[cfg(feature = "perft")]
        Command::Perft {
            position,
            depth,
            divide,
            iterative,
            bench,
            bulk,
            no_board,
        } => {
            let mut position = if let Some(fen) = position {
                Position::from_fen(&fen.parse().unwrap())
            } else {
                Position::initial()
            };

            PerftConfig {
                depth,
                divide,
                iterative,
                bench,
                bulk_counting: bulk,
                show_board: !no_board,
            }
            .go(&mut position)
        }
        #[cfg(not(feature = "perft"))]
        Command::Perft { .. } => {
            eprintln!("Horsey has not been compiled with feature `perft`");
        }
        #[cfg(feature = "train")]
        Command::SelfPlay { games, output } => {
            let records = selfplay::self_play(
                games,
                SearchConfig::new().with_max_nodes(10000).with_workers(1),
            );
            selfplay::save_self_play(output, &records).unwrap();
        }
        #[cfg(not(feature = "train"))]
        Command::SelfPlay { .. } => {
            eprintln!("Horsey has not been compiled with feature `train`");
        }
    }
}
