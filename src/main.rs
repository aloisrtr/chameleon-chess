use chameleon_chess::{
    board::{perft::PerftConfig, position::Position},
    protocols::uci::uci_client,
};
use clap::{Parser, Subcommand};

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Arguments {
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand, Debug)]
enum Command {
    Uci,
    Perft {
        depth: u8,
        #[arg(short, long)]
        position: Option<String>,
        #[arg(short)]
        divide: bool,
        #[arg(short)]
        iterative: bool,
        #[arg(long)]
        bench: bool,
        #[arg(short)]
        bulk: bool,

        #[arg(long)]
        no_board: bool,
    },
}

pub fn main() {
    let args = Arguments::parse();

    match args.command.unwrap_or(Command::Uci) {
        Command::Uci => uci_client().unwrap(),
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
                Position::from_fen(&fen).unwrap()
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
    }
}
