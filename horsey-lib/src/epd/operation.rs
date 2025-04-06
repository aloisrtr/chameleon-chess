//! # Representations for EPD operations (operation codes and operands).

use crate::{
    chess::action::{SanMove, SanParseError},
    parsing::{PartialFromStr, parse_char, parse_i32, parse_string, parse_u32},
};

/// Standard EPD operation code.
///
/// Non-standard operation codes are stored in the `Other` variant.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum EpdOpCode {
    AnalysisCountDepth,
    AnalysisCountNodes,
    AnalysisCountSeconds,
    AvoidMoves,
    BestMoves,
    Comment(u8),
    CentipawnEvaluation,
    DirectMateIn,
    DrawAccept,
    DrawClaim,
    DrawOffer,
    DrawReject,
    EncyclopediaChessOpening,
    FullMoveCounter,
    HalfMoveClock,
    Id,
    NewInChessOpening,
    NoOp,
    PredictedMove,
    PredictedVariation,
    RepetitionCount,
    Resign,
    SuppliedMove,
    NetworkGameSelector,
    NetworkGameReceiver,
    NetworkGameSender,
    Variation(u8),
    Other(heapless::String<14>),
}
impl std::fmt::Display for EpdOpCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use EpdOpCode::*;
        match self {
            AnalysisCountDepth => write!(f, "acd"),
            AnalysisCountNodes => write!(f, "acn"),
            AnalysisCountSeconds => write!(f, "acs"),
            AvoidMoves => write!(f, "am"),
            BestMoves => write!(f, "bm"),
            Comment(i) => write!(f, "c{i}"),
            CentipawnEvaluation => write!(f, "ce"),
            DirectMateIn => write!(f, "dm"),
            DrawAccept => write!(f, "draw_accept"),
            DrawClaim => write!(f, "draw_claim"),
            DrawOffer => write!(f, "draw_offer"),
            DrawReject => write!(f, "draw_reject"),
            EncyclopediaChessOpening => write!(f, "eco"),
            FullMoveCounter => write!(f, "fmvn"),
            HalfMoveClock => write!(f, "hmvc"),
            Id => write!(f, "id"),
            NewInChessOpening => write!(f, "nic"),
            NoOp => write!(f, "noop"),
            PredictedMove => write!(f, "pm"),
            PredictedVariation => write!(f, "pv"),
            RepetitionCount => write!(f, "rc"),
            Resign => write!(f, "resign"),
            SuppliedMove => write!(f, "sm"),
            NetworkGameSelector => write!(f, "tcgs"),
            NetworkGameReceiver => write!(f, "tcri"),
            NetworkGameSender => write!(f, "tcsi"),
            Variation(i) => write!(f, "v{i}"),
            Other(s) => write!(f, "{s}"),
        }
    }
}

#[derive(PartialEq, PartialOrd, Ord, Eq, Clone, Copy, Hash, Debug)]
pub enum EpdOpCodeParseError {
    /// EPD operation codes are limited to 14 characters and are whitespace terminated.
    TooManyCharacters,
    /// An operation code must start with an ASCII alphabetic character (a-zA-Z).
    InvalidFirstCharacter(char),
    /// An operation code cannot be empty.
    EmptyInput,
    /// Some part of the input was left after parsing a valid EPD operation code.
    UnconsumedInput,
}
impl std::fmt::Display for EpdOpCodeParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TooManyCharacters => {
                write!(f, "EPD operation codes are limited to 14 characters")
            }
            Self::InvalidFirstCharacter(c) => write!(
                f,
                "EPD operation codes must start with an ASCII alphabetic character, but got {c}"
            ),
            Self::EmptyInput => write!(f, "Cannot parse an operation code from empty input"),
            Self::UnconsumedInput => write!(
                f,
                "Some part of the input was left after parsing a valid EPD operation code"
            ),
        }
    }
}
impl std::error::Error for EpdOpCodeParseError {}

impl PartialFromStr for EpdOpCode {
    type Err = EpdOpCodeParseError;

    fn partial_from_str(mut s: &str) -> Result<(Self, &str), Self::Err> {
        let mut parsed: heapless::String<14> = heapless::String::new();
        match s.chars().next() {
            Some(c) if c.is_ascii_alphabetic() => {
                parsed.push(c).unwrap();
                s = &s[c.len_utf8()..]
            }
            Some(c) => return Err(EpdOpCodeParseError::InvalidFirstCharacter(c)),
            _ => return Err(EpdOpCodeParseError::EmptyInput),
        }

        while let Some(c) = s.chars().next() {
            if c.is_ascii_alphanumeric() || c == '_' {
                parsed
                    .push(c)
                    .map_err(|_| EpdOpCodeParseError::TooManyCharacters)?;
            } else {
                break;
            }
        }

        let left = &s[parsed.len()..];
        let opcode = match parsed.as_str() {
            "acd" => Self::AnalysisCountDepth,
            "acn" => Self::AnalysisCountNodes,
            "acs" => Self::AnalysisCountSeconds,
            "am" => Self::AvoidMoves,
            "bm" => Self::BestMoves,
            "ce" => Self::CentipawnEvaluation,
            "dm" => Self::DirectMateIn,
            "draw_accept" => Self::DrawAccept,
            "draw_claim" => Self::DrawClaim,
            "draw_offer" => Self::DrawOffer,
            "draw_reject" => Self::DrawReject,
            "eco" => Self::EncyclopediaChessOpening,
            "fmvn" => Self::FullMoveCounter,
            "hmvc" => Self::HalfMoveClock,
            "id" => Self::Id,
            "nic" => Self::NewInChessOpening,
            "noop" => Self::NoOp,
            "pm" => Self::PredictedMove,
            "pv" => Self::PredictedVariation,
            "rc" => Self::RepetitionCount,
            "resign" => Self::Resign,
            "sm" => Self::SuppliedMove,
            "tcgs" => Self::NetworkGameSelector,
            "tcri" => Self::NetworkGameReceiver,
            "tcsi" => Self::NetworkGameSender,
            _ => match parsed.chars().next() {
                Some('c') => parsed
                    .chars()
                    .nth(2)
                    .and_then(|c| c.to_digit(10))
                    .and_then(|i| {
                        if parsed.len() <= 2 {
                            Some(Self::Comment(i as u8))
                        } else {
                            None
                        }
                    })
                    .unwrap_or(Self::Other(parsed)),
                Some('v') => parsed
                    .chars()
                    .nth(2)
                    .and_then(|c| c.to_digit(10))
                    .and_then(|i| {
                        if parsed.len() <= 2 {
                            Some(Self::Variation(i as u8))
                        } else {
                            None
                        }
                    })
                    .unwrap_or(Self::Other(parsed)),
                _ => Self::Other(parsed),
            },
        };

        Ok((opcode, left))
    }
}
impl std::str::FromStr for EpdOpCode {
    type Err = EpdOpCodeParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(op, rest)| {
            if rest.is_empty() {
                Ok(op)
            } else {
                Err(EpdOpCodeParseError::UnconsumedInput)
            }
        })
    }
}

/// Represents values that can serve as operands in EPD operations.
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum EpdOperand {
    String(String),
    Move(SanMove),
    Unsigned(u32),
    Signed(i32),
    Float(f32),
}
impl std::fmt::Display for EpdOperand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use EpdOperand::*;
        match self {
            String(s) => write!(f, "\"{s}\""),
            Move(m) => write!(f, "{m}"),
            Unsigned(i) => write!(f, "{i}"),
            Signed(i) => write!(f, "{i}"),
            Float(n) => write!(f, "{n}"),
        }
    }
}

#[derive(PartialEq, PartialOrd, Ord, Eq, Clone, Copy, Hash, Debug)]
pub enum EpdOperandParseError {
    EmptyInput,
    InvalidUnsignedInt,
    InvalidInteger,
    InvalidStringValue,
    InvalidFloatFractionalPart,
    InvalidSanMove(SanParseError),
    UnconsumedInput,
}
impl std::fmt::Display for EpdOperandParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyInput => write!(f, "Cannot parse operand from empty input"),
            Self::InvalidUnsignedInt => write!(f, "Failed to parse unsigned integer operand"),
            Self::InvalidInteger => write!(f, "Failed to parse integer operand"),
            Self::InvalidStringValue => write!(f, "Failed to parse string operand"),
            Self::InvalidFloatFractionalPart => {
                write!(f, "Failed to parse the fractional part of float operand")
            }
            Self::InvalidSanMove(e) => write!(f, "Failed to parse SAN move operand: {e}"),
            Self::UnconsumedInput => write!(
                f,
                "Some part of the input was left after parsing valid EPD operand"
            ),
        }
    }
}
impl std::error::Error for EpdOperandParseError {}

impl PartialFromStr for EpdOperand {
    type Err = EpdOperandParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        match s.chars().next() {
            Some('"') => parse_string(s)
                .map(|(s, left)| (Self::String(s), left))
                .map_err(|_| EpdOperandParseError::InvalidStringValue),
            Some('-') | Some('+') => {
                let (integer, left) =
                    parse_i32(s).map_err(|_| EpdOperandParseError::InvalidInteger)?;
                if let Some('.') = left.chars().next() {
                    let (fractional, left) = parse_u32(left)
                        .map_err(|_| EpdOperandParseError::InvalidFloatFractionalPart)?;
                    Ok((
                        Self::Float(format!("{integer}.{fractional}").parse().unwrap()),
                        left,
                    ))
                } else {
                    Ok((Self::Signed(integer), left))
                }
            }
            Some(c) if c.is_ascii_digit() => parse_u32(s)
                .map(|(i, s)| (Self::Unsigned(i), s))
                .map_err(|_| EpdOperandParseError::InvalidUnsignedInt),
            Some(_) => SanMove::partial_from_str(s)
                .map(|(m, s)| (Self::Move(m), s))
                .map_err(|e| EpdOperandParseError::InvalidSanMove(e)),
            None => Err(EpdOperandParseError::EmptyInput),
        }
    }
}
impl std::str::FromStr for EpdOperand {
    type Err = EpdOperandParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(op, rest)| {
            if rest.is_empty() {
                Ok(op)
            } else {
                Err(EpdOperandParseError::UnconsumedInput)
            }
        })
    }
}
impl From<u32> for EpdOperand {
    fn from(value: u32) -> Self {
        Self::Unsigned(value)
    }
}
impl From<String> for EpdOperand {
    fn from(value: String) -> Self {
        Self::String(value)
    }
}
impl From<f32> for EpdOperand {
    fn from(value: f32) -> Self {
        Self::Float(value)
    }
}
impl From<i32> for EpdOperand {
    fn from(value: i32) -> Self {
        Self::Signed(value)
    }
}
impl From<SanMove> for EpdOperand {
    fn from(value: SanMove) -> Self {
        Self::Move(value)
    }
}

/// An EPD operation, with its operation code and a list of operands.
///
/// Note that the validity of such combinations is not checked, as user-defined
/// operations can take any number of operands, in any order and with any type.
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub struct EpdOperation {
    pub opcode: EpdOpCode,
    pub operands: Vec<EpdOperand>,
}
impl std::fmt::Display for EpdOperation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.opcode)?;
        for operand in &self.operands {
            write!(f, " {operand}")?
        }
        write!(f, ";")
    }
}

#[derive(PartialEq, PartialOrd, Ord, Eq, Hash, Clone, Copy, Debug)]
pub enum EpdOperationParseError {
    InvalidOpCode(EpdOpCodeParseError),
    MissingSemiColon,
    UnconsumedInput,
}
impl std::fmt::Display for EpdOperationParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidOpCode(e) => write!(f, "Invalid opcode: {e}"),
            Self::MissingSemiColon => write!(f, "Missing semicolon as delimited for EPD operation"),
            Self::UnconsumedInput => write!(
                f,
                "Some part of the input was left after parsing a valid EPD operation"
            ),
        }
    }
}
impl std::error::Error for EpdOperationParseError {}

impl PartialFromStr for EpdOperation {
    type Err = EpdOperationParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let (opcode, s) =
            EpdOpCode::partial_from_str(s).map_err(|e| EpdOperationParseError::InvalidOpCode(e))?;

        let mut operands = vec![];
        let s = if let Ok(mut s) = parse_char(s, ' ') {
            while let Ok((operand, left)) = EpdOperand::partial_from_str(s) {
                operands.push(operand);
                s = if let Ok(s) = parse_char(left, ' ') {
                    s
                } else {
                    break;
                }
            }
            s
        } else {
            s
        };

        let s = parse_char(s, ';').map_err(|_| EpdOperationParseError::MissingSemiColon)?;
        Ok((Self { opcode, operands }, s))
    }
}
impl std::str::FromStr for EpdOperation {
    type Err = EpdOperationParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::partial_from_str(s).and_then(|(epd, rest)| {
            if rest.is_empty() {
                Ok(epd)
            } else {
                Err(EpdOperationParseError::UnconsumedInput)
            }
        })
    }
}
