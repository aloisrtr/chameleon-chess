//! # UCI Commands
//! These are commands that can be sent to another UCI compatible program through
//! an [`UciServerEndpoint`] for messages or [`UciClientEndpoint`] for commands.

use crate::{game::action::Action, protocols::uci::options::UciValue};
use std::{collections::BTreeMap, time::Duration};

use super::{options::UciOptionField, search::UciSearchParameters};

/// Commands that can be received by the client (engine) from the server.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UciCommand {
    Initialize,
    Debug(bool),
    IsReady,
    SetOption {
        name: String,
        value: UciValue,
    },
    RegisterLater,
    RegisterName(String),
    RegisterCode(u64),
    Register {
        name: String,
        code: u64,
    },
    NewGame,
    SetPosition {
        fen: Option<String>,
        moves: Vec<Action>,
    },
    StartSearch(UciSearchParameters),
    StopSearch,

    PonderHit,
    Quit,
}
impl std::fmt::Display for UciCommand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Initialize => writeln!(f, "uci"),
            Self::Debug(on) => writeln!(f, "debug {}", if *on { "on" } else { "off" }),
            Self::IsReady => writeln!(f, "isready"),
            Self::SetOption { name, value } => {
                writeln!(
                    f,
                    "setoption name {name}{}",
                    match value {
                        UciValue::Boolean(b) => format!(" value {b}"),
                        UciValue::Integer(i) => format!(" value {i}"),
                        UciValue::Str(s) => format!(" value {s}"),
                        _ => String::new(),
                    }
                )
            }
            Self::RegisterLater => writeln!(f, "register later"),
            Self::RegisterName(name) => writeln!(f, "register name {name}"),
            Self::RegisterCode(code) => writeln!(f, "register code {code}"),
            Self::Register { name, code } => {
                writeln!(f, "register name {name}")?;
                writeln!(f, "regiter code {code}")
            }
            Self::NewGame => writeln!(f, "ucinewgame"),
            Self::SetPosition { fen, moves } => writeln!(
                f,
                "fen {} moves{}",
                fen.as_ref().unwrap_or(&String::from("startpos")),
                moves
                    .iter()
                    .fold(String::new(), |acc, m| format!("{acc} {m}"))
            ),
            Self::StartSearch(builder) => writeln!(f, "go {}", builder.as_uci_string()),
            Self::StopSearch => writeln!(f, "stop"),
            Self::PonderHit => writeln!(f, "ponderhit"),
            Self::Quit => writeln!(f, "quit"),
        }
    }
}
impl std::str::FromStr for UciCommand {
    type Err = ();

    /// Parses a UCI command in string format.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        let tokens = s.split_whitespace();
        let mut verb = "";
        let mut parameter_name = "";
        let mut parameters = BTreeMap::new();
        for token in tokens {
            match token {
                // Verbs, only the first one parsed is taken into account
                "uci" if verb.is_empty() => return Ok(UciCommand::Initialize),
                "debug" if verb.is_empty() => verb = "debug",
                "isready" if verb.is_empty() => return Ok(UciCommand::IsReady),
                "setoption" if verb.is_empty() => verb = "setoption",
                "register" if verb.is_empty() => verb = "register",
                "ucinewgame" if verb.is_empty() => return Ok(UciCommand::NewGame),
                "position" if verb.is_empty() => verb = "position",
                "go" if verb.is_empty() => verb = "go",
                "stop" if verb.is_empty() => return Ok(UciCommand::StopSearch),
                "ponderhit" if verb.is_empty() => return Ok(UciCommand::PonderHit),
                "quit" if verb.is_empty() => return Ok(UciCommand::Quit),

                // Parameters
                "later" => {
                    if verb == "register" {
                        return Ok(UciCommand::RegisterLater);
                    }
                }
                "startpos" => {
                    parameters.insert("fen", vec![]);
                }
                "name" | "code" | "moves" | "searchmoves" | "wtime" | "btime" | "winc" | "binc"
                | "movestogo" | "depth" | "nodes" | "mate" | "movetime" | "ponder" | "infinite"
                | "value" => {
                    parameters.insert(token, vec![]);
                    parameter_name = token
                }
                "on" if !parameters.contains_key("off") => {
                    parameters.insert("on", vec![]);
                    parameter_name = "on"
                }
                "off" if !parameters.contains_key("on") => {
                    parameters.insert("off", vec![]);
                    parameter_name = "off"
                }

                // Values
                t => {
                    if parameter_name.is_empty() {
                        parameters.insert("fen", vec![]);
                        parameter_name = "fen";
                    }

                    if let Some(values) = parameters.get_mut(parameter_name) {
                        values.push(t)
                    }
                }
            }
        }

        // Actual parsing and building of the resulting command
        Ok(match verb {
            "debug" => {
                if parameters.contains_key("on") {
                    UciCommand::Debug(true)
                } else if parameters.contains_key("off") {
                    UciCommand::Debug(false)
                } else {
                    return Err(());
                }
            }
            "setoption" => {
                let name = parameters.get("name").map(|v| v.join(" ")).ok_or(())?;
                let value = parameters
                    .get("value")
                    .and_then(|v| v.join(" ").parse().ok())
                    .unwrap_or(UciValue::Button);
                UciCommand::SetOption { name, value }
            }
            "register" => {
                let name = parameters.get("name").map(|n| n.join(" "));
                let code = parameters
                    .get("code")
                    .and_then(|c| c.first())
                    .and_then(|c| c.parse().ok());
                if let Some(name) = name {
                    if let Some(code) = code {
                        UciCommand::Register {
                            name: String::from_str(&name).unwrap(),
                            code,
                        }
                    } else {
                        UciCommand::RegisterName(String::from_str(&name).unwrap())
                    }
                } else if let Some(code) = code {
                    UciCommand::RegisterCode(code)
                } else {
                    UciCommand::RegisterLater
                }
            }
            "position" => {
                let fen = String::from_str(&parameters.get("fen").ok_or(())?.join(" ")).unwrap();
                let moves = parameters.get("moves").cloned().unwrap_or(vec![]);
                UciCommand::SetPosition {
                    fen: if fen.is_empty() { None } else { Some(fen) },
                    moves: moves.iter().filter_map(|m| m.parse().ok()).collect(),
                }
            }
            "go" => {
                let search_parameters = UciSearchParameters::default()
                    .with_available_moves(
                        &parameters
                            .get("searchmoves")
                            .unwrap_or(&Vec::new())
                            .iter()
                            .flat_map(|m| m.parse().ok())
                            .collect::<Vec<_>>(),
                    )
                    .set_ponder(parameters.contains_key("ponder"))
                    .with_white_time(
                        parameters
                            .get("wtime")
                            .and_then(|v| {
                                v.first()
                                    .and_then(|d| d.parse().ok().map(Duration::from_millis))
                            })
                            .unwrap_or(Duration::ZERO),
                    )
                    .with_black_time(
                        parameters
                            .get("btime")
                            .and_then(|v| {
                                v.first()
                                    .and_then(|d| d.parse().ok().map(Duration::from_millis))
                            })
                            .unwrap_or(Duration::ZERO),
                    )
                    .with_white_increment(
                        parameters
                            .get("winc")
                            .and_then(|v| {
                                v.first()
                                    .and_then(|d| d.parse().ok().map(Duration::from_millis))
                            })
                            .unwrap_or(Duration::ZERO),
                    )
                    .with_black_increment(
                        parameters
                            .get("binc")
                            .and_then(|v| {
                                v.first()
                                    .and_then(|d| d.parse().ok().map(Duration::from_millis))
                            })
                            .unwrap_or(Duration::ZERO),
                    )
                    .with_moves_until_time_control(
                        parameters
                            .get("movestogo")
                            .and_then(|v| v.first().and_then(|m| m.parse().ok()))
                            .unwrap_or(0),
                    )
                    .with_depth(
                        parameters
                            .get("depth")
                            .and_then(|v| v.first().and_then(|d| d.parse().ok()))
                            .unwrap_or(0),
                    )
                    .with_nodes(
                        parameters
                            .get("nodes")
                            .and_then(|v| v.first().and_then(|n| n.parse().ok()))
                            .unwrap_or(0),
                    )
                    .with_distance_to_mate(
                        parameters
                            .get("mate")
                            .and_then(|v| v.first().and_then(|d| d.parse().ok()))
                            .unwrap_or(0),
                    )
                    .with_search_time(
                        parameters
                            .get("movetime")
                            .and_then(|v| {
                                v.first()
                                    .and_then(|d| d.parse().ok().map(Duration::from_millis))
                            })
                            .unwrap_or(Duration::ZERO),
                    )
                    .set_infinite(parameters.contains_key("infinite"));

                UciCommand::StartSearch(search_parameters)
            }
            _ => return Err(()),
        })
    }
}

/// Messages that can be sent by the engine in response to a command or just
/// for debugging purposes.
#[derive(Clone, PartialEq, Debug)]
pub enum UciMessage {
    Identity {
        name: String,
        author: String,
    },
    Initialized,
    Ready,
    SearchResult {
        best: Action,
        ponder_on: Option<Action>,
    },
    CopyrightCheck,
    CopyrightStatus(bool),
    RegistrationCheck,
    RegistrationStatus(bool),
    Information(Vec<UciInformation>),
    Debug(String),
    Option {
        name: String,
        field: UciOptionField,
    },
}
impl std::fmt::Display for UciMessage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identity { name, author } => {
                writeln!(f, "id name {name}")?;
                writeln!(f, "id author {author}")
            }
            Self::Initialized => writeln!(f, "uciok"),
            Self::Ready => writeln!(f, "readyok"),
            Self::SearchResult { best, ponder_on } => writeln!(
                f,
                "bestmove {best}{}",
                if let Some(m) = ponder_on {
                    format!(" ponder {m}")
                } else {
                    String::new()
                }
            ),
            Self::CopyrightCheck => writeln!(f, "copyprotection checking"),
            Self::CopyrightStatus(ok) => {
                write!(f, "copyprotection {}", if *ok { "ok" } else { "error" })
            }
            Self::RegistrationCheck => writeln!(f, "registration checking"),
            Self::RegistrationStatus(ok) => {
                write!(f, "registration {}", if *ok { "ok" } else { "error" })
            }
            Self::Information(infos) => writeln!(
                f,
                "info{}",
                infos
                    .iter()
                    .fold(String::new(), |acc, info| format!("{acc} {info}"))
            ),
            Self::Debug(msg) => writeln!(f, "info string {msg}"),
            Self::Option { name, field } => writeln!(
                f,
                "option name {name} type {}",
                match &field {
                    UciOptionField::Boolean { default, .. } => format!("check default {default}"),
                    UciOptionField::IntegerRange {
                        min, max, default, ..
                    } => format!("spin default {default} min {min} max {max}"),
                    UciOptionField::Choice {
                        possibilities,
                        default,
                        ..
                    } => format!(
                        "combo default {}{} ",
                        possibilities[*default],
                        possibilities
                            .iter()
                            .fold(String::new(), |acc, o| format!("{acc} {o}"))
                    ),
                    UciOptionField::String { default, .. } => format!("string default {default}"),
                    UciOptionField::Button => "button".to_string(),
                },
            ),
        }
    }
}

/// Information that can be sent from the engine to the server.
#[derive(Clone, PartialEq, Debug)]
pub enum UciInformation {
    SearchDepth(u8),
    SelectiveDepth(u8),
    SearchTime(Duration),
    SearchedNodes(u64),
    PrincipalVariation {
        ranking: Option<u8>,
        moves: Vec<Action>,
    },
    CentipawnScore {
        centipawns: i16,
        is_upper_bound: Option<bool>,
    },
    MateIn {
        moves: i8,
        is_upper_bound: Option<bool>,
    },

    CurrentlySearchedMove {
        move_index: Option<u8>,
        mv: Action,
    },
    HashTableFill(f32),
    SearchSpeed(u64),
    EndgameTableHits(u64),
    ShredderTableHits(u64),
    CpuLoad(f32),
    Debug(String),
    RefutationLine {
        mv: Action,
        refuted_by: Vec<Action>,
    },
    CurrentlySearchedLine {
        on_cpu: usize,
        line: Vec<Action>,
    },
}
impl std::fmt::Display for UciInformation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SearchDepth(depth) => write!(f, "depth {depth}"),
            Self::SelectiveDepth(depth) => write!(f, "seldepth {depth}"),
            Self::SearchTime(duration) => write!(f, "time {}", duration.as_millis()),
            Self::SearchedNodes(nodes) => write!(f, "nodes {nodes}"),
            Self::PrincipalVariation { ranking, moves } => {
                if let Some(ranking) = ranking {
                    write!(f, "multipv {} ", ranking + 1)?
                }
                write!(f, "pv")?;
                for action in moves.iter() {
                    write!(f, " {action}")?
                }
                Ok(())
            }
            Self::CentipawnScore {
                centipawns,
                is_upper_bound,
            } => write!(
                f,
                "score cp {centipawns}{}",
                if let Some(is_upper) = is_upper_bound {
                    if *is_upper {
                        " upperbound"
                    } else {
                        " lowerbound"
                    }
                } else {
                    ""
                }
            ),
            Self::MateIn {
                moves,
                is_upper_bound,
            } => write!(
                f,
                "score mate {moves}{}",
                if let Some(is_upper) = is_upper_bound {
                    if *is_upper {
                        " upperbound"
                    } else {
                        " lowerbound"
                    }
                } else {
                    ""
                }
            ),
            Self::CurrentlySearchedMove { move_index, mv } => {
                if let Some(index) = move_index {
                    write!(f, "currmovenumber {} ", index + 1)?
                }
                write!(f, "currmove {mv}")
            }
            Self::HashTableFill(percent) => write!(f, "hashfull {}", (percent * 10000f32) as u16),
            Self::SearchSpeed(nps) => write!(f, "nps {nps}"),
            Self::EndgameTableHits(n) => write!(f, "tbhits {n}"),
            Self::ShredderTableHits(n) => write!(f, "sbhits {n}"),
            Self::CpuLoad(percent) => write!(f, "cpuload {}", (percent * 10000f32) as u16),
            Self::Debug(str) => write!(f, "string {str}"),
            Self::RefutationLine { mv, refuted_by } => write!(
                f,
                "refutation {mv}{}",
                refuted_by
                    .iter()
                    .fold(String::new(), |acc, m| format!("{acc} {m}"))
            ),
            Self::CurrentlySearchedLine { on_cpu, line } => write!(
                f,
                "currline {on_cpu}{}",
                line.iter()
                    .fold(String::new(), |acc, m| format!("{acc} {m}"))
            ),
        }
    }
}
