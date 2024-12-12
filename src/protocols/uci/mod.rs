//! # Universal Chess Interface
//! The Universal Chess Interface (UCI) protocol was designed by Rudolf Huber and
//! Stefan Meyer-Kahlen and is the most common protocol implement to communicate with
//! modern chess engines.
//!
//! ## Constraints and guarantees
//! - the implementation is **OS-independant**
//! - all communication is done **through standard I/O**
//! - when starting, the engine **waits for the server** (notably `isready` and `setoption` commands)
//! - the engine should **always be able to process standard input**, even during search
//! - all commands sent and received will **end with the newline character**
//! - the engine should never start searching or pondering without receiving a `go` command
//! - all `go` commands are preceded by a `position` command
//! - by default, book management should be done by the server
//! - the implementation should be **fault tolerant**, unexpected tokens or commands should be ignored
//!
//! ## Move format
//! UCI uses **long algebraic notation** for moves, i.e. `<from><to>[promotion]`.

use std::{
    io::Write,
    sync::{Arc, Mutex},
};

use crate::{board::position::Position, search::SearchConfig};

pub mod commands;
pub mod endpoint;

use commands::{UciCommand, UciMessage};
use endpoint::{UciReader, UciWriter};

pub fn uci_client() -> std::io::Result<()> {
    let mut position = Position::initial();
    let mut debug = false;

    let writer = Arc::new(Mutex::new(UciWriter::new(std::io::stdout())));
    let mut reader = UciReader::new(std::io::stdin());
    let mut search_handle = None;

    'uci: loop {
        match reader.read_command() {
            Ok(Some(cmd)) => {
                log::info!("Received command {cmd:?}");
                match cmd {
                    UciCommand::Initialize => initialize_engine(&writer)?,
                    UciCommand::IsReady => send_message(&writer, UciMessage::Ready)?,
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
                                panic!();
                            }
                        }
                    }
                    UciCommand::StartSearch(params) => {
                        if search_handle.is_some() {
                            send_debug_message(&writer, "A search is already running", debug)?;
                            continue;
                        }
                        let config = SearchConfig::from(params);
                        send_debug_message(
                            &writer,
                            format!("Running search with parameters {config:?}"),
                            debug,
                        )?;
                        search_handle = Some(config.go(position.clone(), writer.clone()));
                    }
                    UciCommand::StopSearch => {
                        if let Some(mut handle) = search_handle.take() {
                            handle.stop();
                            match handle.best_action() {
                                Some(best) => send_message(
                                    &writer,
                                    UciMessage::SearchResult {
                                        best: best.downgrade(),
                                        ponder_on: None,
                                    },
                                )?,
                                None => send_debug_message(
                                    &writer,
                                    "Did not find any moves to play",
                                    debug,
                                )?,
                            }
                        }
                    }
                    UciCommand::PonderHit => todo!("pondering is not yet implemented"),
                    UciCommand::Quit => break 'uci,
                    _ => (),
                }
            }

            Ok(None) => send_debug_message(&writer, "Failed to parse command", debug)?,
            Err(e) => eprintln!("Error {e:?}"),
        }
    }

    Ok(())
}

fn initialize_engine<O: Write>(writer: &Arc<Mutex<UciWriter<O>>>) -> std::io::Result<()> {
    let mut writer = writer.lock().unwrap();
    // Register the engine
    writer.send_message(UciMessage::Identity {
        name: String::from("chameleon-chess"),
        author: String::from("Aloïs Rautureau"),
    })?;
    // Send available options
    // uci.send()?;
    // Everything ready!
    writer.send_message(UciMessage::Initialized)
}

fn send_message<O: Write>(
    writer: &Arc<Mutex<UciWriter<O>>>,
    message: UciMessage,
) -> std::io::Result<()> {
    writer.lock().unwrap().send_message(message)
}

fn send_debug_message<O: Write, S: Into<String>>(
    writer: &Arc<Mutex<UciWriter<O>>>,
    message: S,
    debug_on: bool,
) -> std::io::Result<()> {
    if !debug_on {
        return Ok(());
    }

    send_message(writer, UciMessage::Debug(message.into()))
}
