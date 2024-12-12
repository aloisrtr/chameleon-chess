use std::io::{Read, Result, Write};

use chameleon_chess::{
    board::{perft::PerftConfig, position::Position},
    protocols::uci::{
        commands::{UciCommand, UciMessage},
        UciServerEndpoint,
    },
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
        Command::Uci => {
            let mut position = Position::initial();
            let mut debug = false;

            let mut stdout = std::io::stdout();
            let mut stdin = std::io::stdin();
            let mut uci = UciServerEndpoint::new(&mut stdout, &mut stdin);

            'uci: loop {
                match uci.read() {
                    Ok(Some(cmd)) => {
                        log::info!("Received command {cmd:?}");
                        match cmd {
                            UciCommand::Initialize => initialize_engine(&mut uci).unwrap(),
                            UciCommand::IsReady => uci.send(UciMessage::Ready).unwrap(),
                            UciCommand::Debug(on) => debug = on,
                            UciCommand::SetOption { name, value } => {
                                todo!("options are not yet implemented")
                            }
                            UciCommand::NewGame => {
                                todo!()
                            }
                            UciCommand::SetPosition { fen, moves } => {
                                position = if let Some(fen) = fen {
                                    Position::from_fen(&fen).unwrap()
                                } else {
                                    Position::initial()
                                };
                                for m in moves {
                                    if let Err(_) = position.make(m) {
                                        log::error!("Illegal move in position command: {m}");
                                        return;
                                    }
                                }
                            }
                            UciCommand::StartSearch(params) => {
                                todo!()
                            }
                            UciCommand::StopSearch => todo!(),
                            UciCommand::PonderHit => todo!("pondering is not yet implemented"),
                            UciCommand::Quit => break 'uci,
                            _ => (),
                        }
                    }

                    Ok(None) => eprintln!("Failed to parse command"),
                    Err(e) => eprintln!("Error {e:?}"),
                }
            }
        }
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

pub fn initialize_engine<I: Read, O: Write>(uci: &mut UciServerEndpoint<I, O>) -> Result<()> {
    // Register the engine
    uci.send(UciMessage::Identity {
        name: String::from("chameleon-chess"),
        author: String::from("Aloïs Rautureau"),
    })?;
    // Send available options
    // uci.send()?;
    // Everything ready!
    uci.send(UciMessage::Initialized)
}
