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
    borrow::Cow,
    collections::BTreeMap,
    io::Write,
    sync::{Arc, Mutex},
};

use crate::{
    game::position::Position,
    search::{SearchConfig, SearchHandle},
};

pub mod commands;
pub mod endpoint;
pub mod options;
pub mod search;

use commands::{UciCommand, UciMessage};
use endpoint::{UciReader, UciWriter};
use options::{UciOptionField, UciValue};

pub fn uci_client() -> std::io::Result<()> {
    let mut position = Position::initial();
    let mut debug = false;

    let writer = Arc::new(Mutex::new(UciWriter::new(std::io::stdout())));
    let mut reader = UciReader::new(std::io::stdin());
    let mut search_handle: Option<SearchHandle> = None;

    let mut options = setup_options();

    'uci: loop {
        match reader.read_command() {
            Ok(Some(cmd)) => {
                match cmd {
                    UciCommand::Initialize => initialize_engine(&writer, &options)?,
                    UciCommand::IsReady => send_message(&writer, UciMessage::Ready)?,
                    UciCommand::Debug(on) => debug = on,
                    UciCommand::SetOption { name, value } => {
                        if let Some(field) = options.get_mut(name.as_ref()) {
                            field.assign(value).unwrap()
                        }
                    }
                    UciCommand::NewGame => {
                        // TODO: refresh the game tree when implemented correctly
                    }
                    UciCommand::SetPosition { fen, moves } => {
                        position = if let Some(fen) = fen {
                            Position::from_fen(&fen.parse().unwrap())
                        } else {
                            Position::initial()
                        };
                        for m in moves {
                            if position.make(m).is_err() {
                                send_debug_message(
                                    &writer,
                                    format!("Illegal move in position command: {m}, quitting"),
                                    debug,
                                )?;
                                panic!();
                            }
                        }
                        send_debug_message(&writer, format!("{position}"), debug)?
                    }
                    UciCommand::StartSearch(params) => {
                        if let Some(mut handle) = search_handle.take() {
                            handle.stop()
                        }

                        let mut config = SearchConfig::from(params);
                        if let Some(UciValue::Integer(value)) =
                            options.get("SearchWorkers").map(UciOptionField::value)
                        {
                            config = config.with_workers(value as u32)
                        }
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

fn setup_options() -> BTreeMap<String, UciOptionField> {
    let mut options = BTreeMap::new();
    options.insert(
        "SearchWorkers".to_string(),
        UciOptionField::IntegerRange {
            actual: 1,
            default: 1,
            min: 1,
            max: num_cpus::get_physical() as i32,
        },
    );
    options
}

fn initialize_engine<O: Write>(
    writer: &Arc<Mutex<UciWriter<O>>>,
    options: &BTreeMap<String, UciOptionField>,
) -> std::io::Result<()> {
    let mut writer = writer.lock().unwrap();
    // Register the engine
    writer.send_message(UciMessage::Identity {
        name: String::from("chameleon-chess"),
        author: String::from("Aloïs Rautureau"),
    })?;

    // Send available options
    for (name, field) in options.iter() {
        writer.send_message(UciMessage::Option {
            name: Cow::Borrowed(name),
            field: field.clone(),
        })?
    }

    // Everything ready!
    writer.send_message(UciMessage::Initialized)
}

fn send_message<O: Write>(
    writer: &Arc<Mutex<UciWriter<O>>>,
    message: UciMessage,
) -> std::io::Result<()> {
    writer.lock().unwrap().send_message(message)
}

fn send_debug_message<O: Write, S: AsRef<str>>(
    writer: &Arc<Mutex<UciWriter<O>>>,
    message: S,
    debug_on: bool,
) -> std::io::Result<()> {
    if !debug_on {
        return Ok(());
    }

    send_message(writer, UciMessage::Debug(Cow::Borrowed(message.as_ref())))
}
