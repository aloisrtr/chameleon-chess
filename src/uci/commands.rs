//! # UCI Commands/Messages
//! These are commands/messages that can be sent to another UCI compatible program.

use thiserror::Error;

use crate::game::{action::Action, fen::Fen, score::CentiPawns};
use std::{borrow::Cow, time::Duration};

use super::{
    options::{UciOptionField, UciValue},
    search::UciSearchParameters,
};

#[derive(Debug, Clone, Error)]
pub enum UciError<'a> {
    #[error("Unknown command verb: {0}")]
    UnknownCommandVerb(Cow<'a, str>),
    #[error("Empty command")]
    EmptyCommand,
    #[error("Missing parameter: {0}")]
    MissingParameter(&'static str),
    #[error("Invalid parameter: expected {expected}, got {got}")]
    InvalidParameter {
        got: Cow<'a, str>,
        expected: &'static str,
    },
}

/// Commands that can be received by the client (engine) from the server.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UciCommand<'a> {
    Initialize,
    Debug(bool),
    IsReady,
    SetOption {
        name: Cow<'a, str>,
        value: UciValue,
    },
    RegisterLater,
    RegisterName(Cow<'a, str>),
    RegisterCode(u64),
    Register {
        name: Cow<'a, str>,
        code: u64,
    },
    NewGame,
    SetPosition {
        fen: Option<Fen>,
        moves: Vec<Action>,
    },
    StartSearch(UciSearchParameters),
    StopSearch,

    PonderHit,
    Quit,
}
impl std::fmt::Display for UciCommand<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Initialize => writeln!(f, "uci"),
            Self::Debug(on) => writeln!(f, "debug {}", if *on { "on" } else { "off" }),
            Self::IsReady => writeln!(f, "isready"),
            Self::SetOption { name, value } => {
                write!(f, "setoption name {name}")?;

                match value {
                    UciValue::Boolean(b) => writeln!(f, " value {b}"),
                    UciValue::Integer(i) => writeln!(f, " value {i}"),
                    UciValue::Str(s) => writeln!(f, " value {s}"),
                    _ => writeln!(f),
                }
            }
            Self::RegisterLater => writeln!(f, "register later"),
            Self::RegisterName(name) => writeln!(f, "register name {name}"),
            Self::RegisterCode(code) => writeln!(f, "register code {code}"),
            Self::Register { name, code } => {
                writeln!(f, "register name {name}")?;
                writeln!(f, "regiter code {code}")
            }
            Self::NewGame => writeln!(f, "ucinewgame"),
            Self::SetPosition { fen, moves } => {
                write!(
                    f,
                    "fen {} moves",
                    if let Some(fen) = fen {
                        fen.to_string()
                    } else {
                        "startpos".to_string()
                    },
                )?;
                for m in moves {
                    write!(f, " {m}")?
                }
                writeln!(f)
            }
            Self::StartSearch(params) => writeln!(f, "go {}", params.as_uci_string()),
            Self::StopSearch => writeln!(f, "stop"),
            Self::PonderHit => writeln!(f, "ponderhit"),
            Self::Quit => writeln!(f, "quit"),
        }
    }
}
impl<'a> std::str::FromStr for UciCommand<'a> {
    type Err = UciError<'a>;

    /// Parses a UCI command in string format.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.trim();
        let mut tokens = s.split_whitespace().peekable();
        match tokens.next().ok_or(UciError::EmptyCommand)? {
            "uci" => Ok(UciCommand::Initialize),
            "debug" => {
                match tokens
                    .next()
                    .ok_or(UciError::MissingParameter("[on | off]"))?
                {
                    "on" => Ok(UciCommand::Debug(true)),
                    "off" => Ok(UciCommand::Debug(false)),
                    p => Err(UciError::InvalidParameter {
                        got: Cow::Owned(p.to_string()),
                        expected: "[on | off]",
                    }),
                }
            }
            "isready" => Ok(UciCommand::IsReady),
            "setoption" => {
                match tokens
                    .next()
                    .ok_or(UciError::MissingParameter("name <name>"))?
                {
                    "name" => {
                        let mut name = String::new();
                        let mut value = None;
                        for token in tokens {
                            match token {
                                "value" => value = Some(String::new()),
                                s => {
                                    if let Some(value) = &mut value {
                                        value.push(' ');
                                        value.push_str(s);
                                    } else {
                                        name.push(' ');
                                        name.push_str(s);
                                    }
                                }
                            }
                        }
                        Ok(UciCommand::SetOption {
                            name: Cow::Owned(name),
                            value: if let Some(value) = value {
                                UciValue::from_str(&value).unwrap()
                            } else {
                                UciValue::Button
                            },
                        })
                    }
                    p => Err(UciError::InvalidParameter {
                        got: Cow::Owned(p.to_string()),
                        expected: "name <name>",
                    }),
                }
            }
            "register" => {
                let mut name = None;
                let mut code = None;
                let mut current_parse = None;
                for token in tokens {
                    match token {
                        "later" => {
                            return if current_parse.is_none() {
                                Ok(UciCommand::RegisterLater)
                            } else {
                                Err(UciError::InvalidParameter {
                                    got: Cow::Borrowed("later"),
                                    expected: "cannot use later with name and/or code",
                                })
                            }
                        }
                        "name" => {
                            name = Some(String::new());
                            current_parse = Some(&mut name);
                        }
                        "code" => {
                            code = Some(String::new());
                            current_parse = Some(&mut code)
                        }
                        s => {
                            if let Some(Some(current)) = current_parse {
                                current.push(' ');
                                current.push_str(s);
                            } else {
                                return Err(UciError::MissingParameter(
                                    "[later | name <name> | code <code>]",
                                ));
                            }
                        }
                    }
                }
                match (name, code) {
                    (Some(name), Some(code)) => Ok(UciCommand::Register {
                        name: Cow::Owned(name),
                        code: code.parse().map_err(|_| UciError::InvalidParameter {
                            got: Cow::Owned(code),
                            expected: "integer",
                        })?,
                    }),
                    (Some(name), _) => Ok(UciCommand::RegisterName(Cow::Owned(name))),
                    (_, Some(code)) => {
                        Ok(UciCommand::RegisterCode(code.parse().map_err(|_| {
                            UciError::InvalidParameter {
                                got: Cow::Owned(code),
                                expected: "integer",
                            }
                        })?))
                    }
                    (_, _) => Err(UciError::MissingParameter(
                        "[later | name <name> | code <code>]",
                    )),
                }
            }
            "ucinewgame" => Ok(UciCommand::NewGame),
            "position" => {
                let mut fen = String::new();
                let mut moves = vec![];
                match tokens
                    .next()
                    .ok_or(UciError::MissingParameter("[<fen> | startpos]"))?
                {
                    "startpos" => (),
                    s => {
                        fen.push_str(s);
                        while let Some(token) = tokens.next_if(|token| *token != "moves") {
                            fen.push(' ');
                            fen.push_str(token);
                        }
                    }
                }
                match tokens
                    .next()
                    .ok_or(UciError::MissingParameter("moves <moves>"))?
                {
                    "moves" => {
                        for token in tokens {
                            moves.push(token.parse().map_err(|_| UciError::InvalidParameter {
                                got: Cow::Owned(token.to_string()),
                                expected: "move",
                            })?);
                        }
                        Ok(UciCommand::SetPosition {
                            fen: if fen.is_empty() {
                                None
                            } else {
                                Some(Fen::parse(&fen).map_err(|_| UciError::InvalidParameter {
                                    got: Cow::Owned(fen),
                                    expected: "FEN string",
                                })?)
                            },
                            moves,
                        })
                    }
                    p => Err(UciError::InvalidParameter {
                        got: Cow::Owned(p.to_string()),
                        expected: "moves <moves>",
                    }),
                }
            }
            "go" => {
                let mut params = UciSearchParameters::new();
                while let Some(token) = tokens.next() {
                    match token {
                        "searchmoves" => {
                            let mut moves = vec![];
                            while let Some(token) = tokens.next_if(|t| matches!(*t, "ponder" | "wtime" | "btime" | "winc" | "binc" | "movestogo" | "depth" | "nodes" | "mate" | "movetime" | "infinite" | "searchmoves")) {
                                        let m = token.parse().map_err(|_| UciError::InvalidParameter { got: Cow::Owned(token.to_string()), expected: "move" })?;
                                        moves.push(m);

                            }
                            params = params.with_available_moves(&moves)
                        }
                        "ponder" => {
                            params = params.set_ponder(true)
                        }
                        "wtime" => {
                            let time_str = tokens.next().ok_or(UciError::MissingParameter("time as ms"))?;
                            let time = time_str.parse().map_err(|_| UciError::InvalidParameter { got: Cow::Owned(time_str.to_string()), expected: "time as ms" })?;
                            params = params.with_white_time(Duration::from_millis(time))
                        }
                        "btime" => {
                            let time_str = tokens.next().ok_or(UciError::MissingParameter("time as ms"))?;
                            let time = time_str.parse().map_err(|_| UciError::InvalidParameter { got: Cow::Owned(time_str.to_string()), expected: "time as ms" })?;
                            params = params.with_black_time(Duration::from_millis(time))
                        }
                        "winc" => {
                            let time_str = tokens.next().ok_or(UciError::MissingParameter("time as ms"))?;
                            let time = time_str.parse().map_err(|_| UciError::InvalidParameter { got: Cow::Owned(time_str.to_string()), expected: "time as ms" })?;
                            params = params.with_white_increment(Duration::from_millis(time))
                        }
                        "binc" => {
                            let time_str = tokens.next().ok_or(UciError::MissingParameter("time as ms"))?;
                            let time = time_str.parse().map_err(|_| UciError::InvalidParameter { got: Cow::Owned(time_str.to_string()), expected: "time as ms" })?;
                            params = params.with_black_increment(Duration::from_millis(time))
                        }
                        "movestogo" => {
                            let int_str = tokens.next().ok_or(UciError::MissingParameter("integer"))?;
                            let value = int_str.parse().map_err(|_| UciError::InvalidParameter { got: Cow::Owned(int_str.to_string()), expected: "integer" })?;
                            params = params.with_moves_until_time_control(value);
                        }
                        "depth" => {
                            let int_str = tokens.next().ok_or(UciError::MissingParameter("integer"))?;
                            let value = int_str.parse().map_err(|_| UciError::InvalidParameter { got: Cow::Owned(int_str.to_string()), expected: "integer" })?;
                            params = params.with_depth(value);
                        }
                        "nodes" => {
                            let int_str = tokens.next().ok_or(UciError::MissingParameter("integer"))?;
                            let value = int_str.parse().map_err(|_| UciError::InvalidParameter { got: Cow::Owned(int_str.to_string()), expected: "integer" })?;
                            params = params.with_nodes(value);
                        }
                        "mate" => {
                            let int_str = tokens.next().ok_or(UciError::MissingParameter("integer"))?;
                            let value = int_str.parse().map_err(|_| UciError::InvalidParameter { got: Cow::Owned(int_str.to_string()), expected: "integer" })?;
                            params = params.with_distance_to_mate(value);
                        }
                        "movetime" => {
                            let time_str = tokens.next().ok_or(UciError::MissingParameter("time as ms"))?;
                            let time = time_str.parse().map_err(|_| UciError::InvalidParameter { got: Cow::Owned(time_str.to_string()), expected: "time as ms" })?;
                            params = params.with_search_time(Duration::from_millis(time))
                        }
                        "infinite" => {
                            params = params.set_infinite(true)
                        }
                        p => Err(UciError::InvalidParameter { got: Cow::Owned(p.to_string()), expected: "[searchmoves <moves> | ponder | wtime <ms> | btime <ms> | winc <ms> | binc <ms> | movestogo <n> | depth <n> | nodes <n> | mate <n> | movetime <ms> | infinite]" })?
                    }
                }
                Ok(UciCommand::StartSearch(params))
            }
            "stop" => Ok(UciCommand::StopSearch),
            "ponderhit" => Ok(UciCommand::PonderHit),
            "quit" => Ok(UciCommand::Quit),
            verb => Err(UciError::UnknownCommandVerb(Cow::Owned(verb.to_string()))),
        }
    }
}

/// Messages that can be sent by the engine in response to a command or just
/// for debugging purposes.
#[derive(Clone, PartialEq, Debug)]
pub enum UciMessage<'a> {
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
    Information(Vec<UciInformation<'a>>),
    Debug(Cow<'a, str>),
    Option {
        name: Cow<'a, str>,
        field: UciOptionField,
    },
}
impl std::fmt::Display for UciMessage<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identity { name, author } => {
                writeln!(f, "id name {name}")?;
                writeln!(f, "id author {author}")
            }
            Self::Initialized => writeln!(f, "uciok"),
            Self::Ready => writeln!(f, "readyok"),
            Self::SearchResult { best, ponder_on } => {
                write!(f, "bestmove {best}",)?;
                if let Some(m) = ponder_on {
                    writeln!(f, " ponder {m}")
                } else {
                    writeln!(f)
                }
            }
            Self::CopyrightCheck => writeln!(f, "copyprotection checking"),
            Self::CopyrightStatus(ok) => {
                write!(f, "copyprotection {}", if *ok { "ok" } else { "error" })
            }
            Self::RegistrationCheck => writeln!(f, "registration checking"),
            Self::RegistrationStatus(ok) => {
                write!(f, "registration {}", if *ok { "ok" } else { "error" })
            }
            Self::Information(infos) => {
                write!(f, "info")?;
                for info in infos {
                    write!(f, " {info}")?
                }
                writeln!(f)
            }
            Self::Debug(msg) => writeln!(f, "info string {msg}"),
            Self::Option { name, field } => {
                write!(f, "option name {name} type ",)?;
                match &field {
                    UciOptionField::Boolean { default, .. } => {
                        writeln!(f, "check default {default}")
                    }
                    UciOptionField::IntegerRange {
                        min, max, default, ..
                    } => writeln!(f, "spin default {default} min {min} max {max}"),
                    UciOptionField::Choice {
                        possibilities,
                        default,
                        ..
                    } => {
                        write!(f, "combo default {}", possibilities[*default],)?;
                        for possibility in possibilities {
                            write!(f, " {possibility}")?;
                        }
                        writeln!(f)
                    }
                    UciOptionField::String { default, .. } => {
                        writeln!(f, "string default {default}")
                    }
                    UciOptionField::Button => writeln!(f, "button"),
                }
            }
        }
    }
}

/// Information that can be sent from the engine to the server.
#[derive(Clone, PartialEq, Debug)]
pub enum UciInformation<'a> {
    SearchDepth(u8),
    SelectiveDepth(u8),
    SearchTime(Duration),
    SearchedNodes(u64),
    PrincipalVariation {
        ranking: Option<u8>,
        moves: Vec<Action>,
    },
    CentipawnScore {
        centipawns: CentiPawns,
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
    String(Cow<'a, str>),
    RefutationLine {
        mv: Action,
        refuted_by: Vec<Action>,
    },
    CurrentlySearchedLine {
        on_cpu: usize,
        line: Vec<Action>,
    },
}
impl std::fmt::Display for UciInformation<'_> {
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
            Self::String(str) => write!(f, "string {str}"),
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
