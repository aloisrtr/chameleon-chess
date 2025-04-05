//! # Various EPD operations

use crate::{
    chess::action::SanMove,
    parsing::{PartialFromStr, parse_i32, parse_string, parse_u32},
};

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
impl PartialFromStr for EpdOpCode {
    type Err = ();
    fn partial_from_str(mut s: &str) -> Result<(Self, &str), Self::Err> {
        let mut parsed: heapless::String<14> = heapless::String::new();
        match s.chars().next() {
            Some(c) if c.is_ascii_alphabetic() => {
                parsed.push(c).unwrap();
                s = &s[c.len_utf8()..]
            }
            // TODO: better error here
            _ => return Err(()),
        }

        while let Some(c) = s.chars().next() {
            if c.is_ascii_alphanumeric() || c == '_' {
                // TODO: better error
                parsed.push(c).map_err(|_| ())?;
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
                    .map(|i| Self::Comment(i as u8))
                    .unwrap_or(Self::Other(parsed)),
                Some('v') => parsed
                    .chars()
                    .nth(2)
                    .and_then(|c| c.to_digit(10))
                    .map(|i| Self::Comment(i as u8))
                    .unwrap_or(Self::Other(parsed)),
                _ => Self::Other(parsed),
            },
        };

        Ok((opcode, left))
    }
}

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
impl PartialFromStr for EpdOperand {
    type Err = ();

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        match s.chars().next() {
            Some('"') => parse_string(s).map(|(s, left)| (Self::String(s), left)),
            Some('-') | Some('+') => {
                let (integer, left) = parse_i32(s)?;
                if let Some('.') = left.chars().next() {
                    let (fractional, left) = parse_u32(left)?;
                    Ok((
                        Self::Float(format!("{integer}.{fractional}").parse().unwrap()),
                        left,
                    ))
                } else {
                    Ok((Self::Signed(integer), left))
                }
            }
            Some(c) if c.is_ascii_digit() => parse_u32(s).map(|(i, s)| (Self::Unsigned(i), s)),
            _ => SanMove::partial_from_str(s)
                .map(|(m, s)| (Self::Move(m), s))
                .map_err(|_| ()),
        }
    }
}

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
impl PartialFromStr for EpdOperation {
    type Err = ();

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let (opcode, s) = EpdOpCode::partial_from_str(s)?;
        let mut s = if let Some(' ') = s.chars().next() {
            &s[1..]
        } else {
            return Err(());
        };
        let mut operands = vec![];
        while let Ok((operand, left)) = EpdOperand::partial_from_str(s) {
            operands.push(operand);
            s = left
        }

        let s = if let Some(';') = s.chars().next() {
            &s[1..]
        } else {
            return Err(());
        };

        Ok((Self { opcode, operands }, s))
    }
}
