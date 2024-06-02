//! The Universal Chess Interface (UCI) protocol was designed by Rudolf Huber and
//! Stefan Meyer-Kahlen and is the most common protocol implement to communicate with
//! modern chess engines.
//!
//! The specification is OS independant, and handles a lot of "tidy work" that
//! CECP leaves to the engine like pondering, book moves, etc.

//! Commands that can be received by the engine from the controller.

use std::time::Duration;

use crate::r#move::Move;
pub enum UciCommands {
    Initialize,
    Debug(bool),
    IsReady,
    SetOption {
        name: String,
        value: Option<String>,
    },
    // TODO registration
    NewGame,
    SetPosition {
        fen: Option<String>,
        moves: Vec<Move>,
    },
    StartSearch {},
    StopSearch,

    PonderHit,
    Quit,
}
impl std::fmt::Display for UciCommands {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Initialize => write!(f, "uci"),
            Self::Debug(on) => write!(f, "debug {}", if *on { "on" } else { "off" }),
            Self::IsReady => write!(f, "isready"),
            Self::SetOption { name, value } => todo!(),

            Self::NewGame => write!(f, "ucinewgame"),
            Self::SetPosition { fen, moves } => write!(
                f,
                "fen {} moves{}",
                fen.unwrap_or("startpos".to_string()),
                moves
                    .iter()
                    .fold(String::new(), |acc, m| format!("{acc} m"))
            ),
            Self::StartSearch {} => write!(f, "go"),
            Self::StopSearch => write!(f, "stop"),
            Self::PonderHit => write!(f, "ponderhit"),
            Self::Quit => write!(f, "quit"),
        }
    }
}
impl std::str::FromStr for UciCommands {
    type Err = ();

    /// Parses a UCI command in string format.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        todo!()
    }
}

/// Messages that can be sent by the engine in response to a command or just
/// for debugging purposes.
pub enum UciMessage {
    Identity,
    Initialized,
    Ready,
    SearchResult { best: Move, ponder_on: Option<Move> },
    CopyrightCheck,
    CopyrightStatus(bool),
    RegistrationCheck,
    RegistrationStatus(bool),
    Information(Vec<UciInformation>),
    Option(UciOption),
}
impl std::fmt::Display for UciMessage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Identity => write!(f, "id name chameleon-chess author Aloïs R"),
            Self::Initialized => write!(f, "uciok"),
            Self::Ready => write!(f, "readyok"),
            Self::SearchResult { best, ponder_on } => write!(
                f,
                "bestmove {best}{}",
                if let Some(m) = ponder_on {
                    format!(" ponder {m}")
                } else {
                    String::new()
                }
            ),
            Self::CopyrightCheck => write!(f, "copyprotection checking"),
            Self::CopyrightStatus(ok) => {
                write!(f, "copyprotection {}", if *ok { "ok" } else { "error" })
            }
            Self::RegistrationCheck => write!(f, "registration checking"),
            Self::RegistrationStatus(ok) => {
                write!(f, "registration {}", if *ok { "ok" } else { "error" })
            }
            Self::Information(infos) => write!(
                f,
                "info{}",
                infos
                    .iter()
                    .fold(String::new(), |acc, info| format!("{acc} {info}"))
            ),
            Self::Option(option) => write!(f, "option {option}"),
        }
    }
}

pub enum UciInformation {
    SearchDepth(u8),
    SelectiveDepth(u8),
    SearchTime(Duration),
    SearchedNodes(u64),
    PrincipalVariation {
        ranking: u8,
        moves: Vec<Move>,
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
        move_index: u8,
        mv: Move,
    },
    HashTableFill(f32),
    SearchSpeed(u64),
    EndgameTableHits(u64),
    ShredderTableHits(u64),
    CpuLoad(f32),
    Debug(String),
    RefutationLine {
        mv: Move,
        refuted_by: Vec<Move>,
    },
    CurrentlySearchedLine {
        on_cpu: usize,
        line: Vec<Move>,
    },
}
impl std::fmt::Display for UciInformation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SearchDepth(depth) => write!(f, "depth {depth}"),
            Self::SelectiveDepth(depth) => write!(f, "seldepth {depth}"),
            Self::SearchTime(duration) => write!(f, "time {}", duration.as_millis()),
            Self::SearchedNodes(nodes) => write!(f, "nodes {nodes}"),
            Self::PrincipalVariation { ranking, moves } => write!(
                f,
                "multipv {} pv{}",
                ranking + 1,
                moves
                    .iter()
                    .fold(String::new(), |acc, m| format!("{acc} {m}"))
            ),
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
                write!(f, "currmovenumber {} currmove {mv}", move_index + 1)
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
