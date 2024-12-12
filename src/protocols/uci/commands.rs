//! # UCI Commands
//! These are commands that can be sent to another UCI compatible program through
//! an [`UciServerEndpoint`] for messages or [`UciClientEndpoint`] for commands.

use crate::board::action::Action;
use std::{
    collections::BTreeMap,
    convert::Infallible,
    num::{NonZeroU64, NonZeroU8},
    time::Duration,
};

/// Commands that can be received by the client (engine) from the server.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UciCommand {
    Initialize,
    Debug(bool),
    IsReady,
    SetOption {
        name: String,
        value: Option<UciValue>,
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
                        Some(UciValue::Boolean(b)) => format!(" value {b}"),
                        Some(UciValue::Integer(i)) => format!(" value {i}"),
                        Some(UciValue::Str(s)) => format!(" value {s}"),
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
                let name = parameters
                    .get("name")
                    .map(|v| String::from(v.join(" ")))
                    .ok_or(())?;
                let value = parameters
                    .get("value")
                    .and_then(|v| v.join(" ").parse().ok());
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
                    .set_ponder(parameters.get("ponder").is_some())
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
                    .set_infinite(parameters.get("infinite").is_some());

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
    Option(UciOption),
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
            Self::Option(option) => writeln!(
                f,
                "option name {} type {}",
                &option.name,
                match &option.value {
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

/// A builder to create clean parameters of search from the server to the engine.
#[derive(Clone, PartialEq, Eq, Default, Debug)]
pub struct UciSearchParameters {
    pub(crate) available_moves: Vec<Action>,
    pub(crate) ponder: bool,
    pub(crate) white_time: Option<Duration>,
    pub(crate) black_time: Option<Duration>,
    pub(crate) white_increment: Option<Duration>,
    pub(crate) black_increment: Option<Duration>,
    pub(crate) moves_until_time_control: Option<NonZeroU8>,
    pub(crate) depth: Option<NonZeroU8>,
    pub(crate) nodes: Option<NonZeroU64>,
    pub(crate) distance_to_mate: Option<NonZeroU8>,
    pub(crate) search_time: Option<Duration>,
    pub(crate) infinite: bool,
}
impl UciSearchParameters {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn with_available_moves(mut self, moves: &[Action]) -> Self {
        self.available_moves = Vec::from(moves);
        self
    }
    pub fn set_ponder(mut self, ponder: bool) -> Self {
        self.ponder = ponder;
        self
    }
    pub fn with_time_constraint(mut self, time: Duration) -> Self {
        self.white_time = if time.is_zero() { None } else { Some(time) };
        self
    }
    pub fn with_white_time(mut self, time: Duration) -> Self {
        self.black_time = if time.is_zero() { None } else { Some(time) };
        self
    }
    pub fn with_black_time(mut self, time: Duration) -> Self {
        self.black_time = if time.is_zero() { None } else { Some(time) };
        self
    }
    pub fn with_white_increment(mut self, increment: Duration) -> Self {
        self.white_increment = if increment.is_zero() {
            None
        } else {
            Some(increment)
        };
        self
    }
    pub fn with_black_increment(mut self, increment: Duration) -> Self {
        self.black_increment = if increment.is_zero() {
            None
        } else {
            Some(increment)
        };
        self
    }
    pub fn with_moves_until_time_control(mut self, moves: u8) -> Self {
        if let Some(moves) = NonZeroU8::new(moves) {
            self.moves_until_time_control = Some(moves)
        } else {
            self.moves_until_time_control = None
        }
        self
    }
    pub fn with_depth(mut self, depth: u8) -> Self {
        if let Some(depth) = NonZeroU8::new(depth) {
            self.depth = Some(depth)
        } else {
            self.depth = None
        }
        self
    }
    pub fn with_nodes(mut self, nodes: u64) -> Self {
        if let Some(nodes) = NonZeroU64::new(nodes) {
            self.nodes = Some(nodes)
        } else {
            self.nodes = None
        }
        self
    }
    pub fn with_distance_to_mate(mut self, distance: u8) -> Self {
        if let Some(distance) = NonZeroU8::new(distance) {
            self.distance_to_mate = Some(distance)
        } else {
            self.distance_to_mate = None
        }
        self
    }
    pub fn with_search_time(mut self, time: Duration) -> Self {
        self.search_time = if time.is_zero() { None } else { Some(time) };
        self
    }
    pub fn set_infinite(mut self, infinite: bool) -> Self {
        self.infinite = infinite;
        self
    }

    pub fn as_uci_string(&self) -> String {
        let mut uci = String::new();
        if !self.available_moves.is_empty() {
            uci = format!(
                "{uci}searchmoves {} ",
                self.available_moves
                    .iter()
                    .fold(String::new(), |acc, m| format!("{acc} {m}"))
            )
        }
        if self.ponder {
            uci = format!("{uci}ponder ")
        }
        if let Some(time) = self.white_time {
            uci = format!("{uci}wtime {} ", time.as_millis())
        }
        if let Some(time) = self.black_time {
            uci = format!("{uci}btime {} ", time.as_millis())
        }
        if let Some(increment) = self.white_increment {
            uci = format!("{uci}winc {} ", increment.as_millis())
        }
        if let Some(increment) = self.black_increment {
            uci = format!("{uci}binc {} ", increment.as_millis())
        }
        if let Some(moves) = self.moves_until_time_control {
            uci = format!("{uci}movestogo {moves} ")
        }
        if let Some(depth) = self.depth {
            uci = format!("{uci}depth {depth} ")
        }
        if let Some(nodes) = self.nodes {
            uci = format!("{uci}nodes {nodes} ")
        }
        if let Some(distance) = self.distance_to_mate {
            uci = format!("{uci}mate {distance} ")
        }
        if let Some(search_time) = self.search_time {
            uci = format!("{uci}movetime {} ", search_time.as_millis())
        }
        if self.infinite {
            uci = format!("{uci}infinite")
        }
        uci
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

/// The different types of UCI fields available.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UciOptionField {
    Boolean {
        actual: bool,
        default: bool,
    },
    IntegerRange {
        actual: i32,
        default: i32,
        min: i32,
        max: i32,
    },
    Choice {
        default: usize,
        actual: usize,
        possibilities: Vec<String>,
    },
    String {
        default: String,
        actual: String,
    },
    Button,
}

/// The different types of UCI values available.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum UciValue {
    Boolean(bool),
    Integer(i32),
    Str(String),
    Button,
}
impl std::str::FromStr for UciValue {
    type Err = Infallible;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(if let Ok(b) = s.parse::<bool>() {
            Self::Boolean(b)
        } else if let Ok(i) = s.parse::<i32>() {
            Self::Integer(i)
        } else if !s.is_empty() {
            Self::Str(String::from_str(s).unwrap())
        } else {
            Self::Button
        })
    }
}

/// Defines an UCI option that can be set by the server on the engine.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct UciOption {
    pub name: String,
    pub value: UciOptionField,
}
