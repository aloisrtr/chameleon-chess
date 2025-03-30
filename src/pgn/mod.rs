//! # Portable Game Notation standard implementation
//! The implementation follows the 2023-03-22 revision of the PGN standard which
//! can be found [here](https://github.com/fsmosca/PGN-Standard/blob/master/PGN-Standard.txt).

use std::fmt::{Arguments, Write};

use thiserror::Error;

use crate::parsing::PartialFromStr;

use super::chess::{
    action::SanMove,
    colour::Colour,
    position::{DrawKind, GameResult},
};

mod parse;
use parse::*;

// pub mod nag;

/// Tag pair representation for contextual game information.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PgnTagPair {
    pub tag: String,
    pub value: String,
}
impl Ord for PgnTagPair {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Ordering follows the standard in that the STR values appear first and in
        // order, then additionnal tags in alphabetical order.
        fn tag_priority(tag: &str) -> Option<u8> {
            Some(match tag {
                "Event" => 0,
                "Site" => 1,
                "Date" => 2,
                "Round" => 3,
                "White" => 4,
                "Black" => 5,
                "Result" => 6,
                _ => return None,
            })
        }
        let self_prio = tag_priority(&self.tag);
        let other_prio = tag_priority(&other.tag);
        match (self_prio, other_prio) {
            (Some(_), None) => std::cmp::Ordering::Less,
            (None, Some(_)) => std::cmp::Ordering::Greater,
            (Some(a), Some(b)) => a.cmp(&b),
            (None, None) => self.tag.cmp(&other.tag),
        }
    }
}
impl PartialOrd for PgnTagPair {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug, Clone, Copy, Error, PartialEq, Eq, Hash)]
pub enum PgnTagPairParseError {
    #[error("Missing opening bracket")]
    MissingOpeningBracket,
    #[error("Invalid tag")]
    InvalidTag,
    #[error("Invalid value")]
    InvalidValue,
    #[error("Missing closing bracket")]
    MissingClosingBracket,
}

impl PartialFromStr for PgnTagPair {
    type Err = PgnTagPairParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        if let Some('[') = s.chars().next() {
            let s = walk_whitespace_and_comments(&s[1..]);
            let (tag, s) = parse_tag(s).map_err(|_| PgnTagPairParseError::InvalidTag)?;
            let s = walk_whitespace_and_comments(s);
            let (value, s) = parse_string(s).map_err(|_| PgnTagPairParseError::InvalidValue)?;
            let s = walk_whitespace_and_comments(s);
            if let Some(']') = s.chars().next() {
                Ok((PgnTagPair { tag, value }, &s[1..]))
            } else {
                Err(PgnTagPairParseError::MissingClosingBracket)
            }
        } else {
            Err(PgnTagPairParseError::MissingOpeningBracket)
        }
    }
}
impl std::fmt::Display for PgnTagPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{} \"{}\"]", self.tag, self.value)
    }
}

/// Represents a single move and any number of following moves within a PGN movetext
/// section.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub struct PgnMove {
    pub halfmove: u16,
    pub mv: SanMove,
    pub nag: u8,
    pub main_child: Option<usize>,
    pub ravs: Vec<usize>,
}
impl PgnMove {
    pub fn fullmove(&self) -> u16 {
        (self.halfmove / 2) + 1
    }

    pub fn white_to_play(&self) -> bool {
        self.halfmove % 2 == 0
    }
}

/// Movetext structure with support for RAV (variations) and NAG (annotations).
///
/// It is represented as a tree of [`PgnMoveTextNode`]s, with index `0` as its root.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash, Default)]
pub struct PgnMoveText {
    moves: Vec<PgnMove>,
    pub result: Option<GameResult>,
}
impl PgnMoveText {
    /// Registers a move within this [`PgnMoveText`], returning its corresponding ID.
    pub fn add_move(&mut self, mv: SanMove) -> usize {
        self.moves.push(PgnMove {
            halfmove: 0,
            mv,
            nag: 0,
            main_child: None,
            ravs: vec![],
        });
        self.moves.len() - 1
    }

    /// Reference to the move corresponding to the given index.
    pub fn get_move(&self, index: usize) -> &PgnMove {
        &self.moves[index]
    }

    /// Mutable reference to the move corresponding to the given index.
    pub fn get_move_mut(&mut self, index: usize) -> &mut PgnMove {
        &mut self.moves[index]
    }
}

#[derive(Debug, Clone, Copy, Error, PartialEq, Eq, Hash)]
pub enum PgnMoveTextParseError {
    #[error("Incoherent move numbering: parent is {expected}, child is {got}")]
    IncoherentMoveNumbering { expected: u16, got: u16 },
    #[error("Recursive Annotation Variation started without root")]
    RavWithoutRoot,
    #[error("Recursive Annotation Variation ended, but never started")]
    EndedNonStartedRav,
    #[error("Numeric Anotation Glyph with no parent move")]
    NagWithNoParentMove,
    #[error("Invalid character for PGN movetext: {0}")]
    InvalidCharacter(char),
    #[error("Missing game result in PGN movetext")]
    MissingGameResult,
}

impl PartialFromStr for PgnMoveText {
    type Err = PgnMoveTextParseError;

    fn partial_from_str(mut s: &str) -> Result<(Self, &str), Self::Err> {
        let mut result = PgnMoveText::default();
        let mut current_node_stack: Vec<Option<usize>> = vec![None];
        let mut current_move_number = 0;
        loop {
            s = walk_whitespace_and_comments(s);
            if let Ok((game_result, left)) = parse_game_result(s) {
                result.result = game_result;
                s = left;
                break;
            }
            match s.chars().next() {
                Some(c) if c.is_digit(10) => {
                    let (move_num, left) = parse_int(s).unwrap();
                    s = left;
                    current_move_number = (move_num - 1) * 2
                }
                Some('.') => {
                    s = &s[1..];
                }
                Some('(') => {
                    if current_node_stack.last().unwrap().is_none() {
                        Err(PgnMoveTextParseError::RavWithoutRoot)?;
                    }
                    current_node_stack.push(None);
                    s = &s[1..];
                }
                Some(')') => {
                    current_node_stack.pop();
                    if let Some(&Some(parent_index)) = current_node_stack.last() {
                        current_move_number = result.get_move(parent_index).halfmove;
                    } else {
                        Err(PgnMoveTextParseError::EndedNonStartedRav)?;
                    }
                    s = &s[1..];
                }
                Some('$') => {
                    let Ok((nag, left)) = parse_int(&s[1..]) else {
                        break;
                    };
                    s = left;
                    if let Some(&Some(parent_index)) = current_node_stack.last() {
                        let parent = result.get_move_mut(parent_index);
                        parent.nag = nag as u8;
                    } else {
                        return Err(PgnMoveTextParseError::NagWithNoParentMove)?;
                    }
                }
                Some(c) => {
                    let (san_move, left) = SanMove::partial_from_str(s)
                        .map_err(|_| PgnMoveTextParseError::InvalidCharacter(c))?;
                    s = left;
                    let node_index = result.add_move(san_move);
                    if let Some(Some(parent_index)) = current_node_stack.pop() {
                        let parent = result.get_move_mut(parent_index);
                        parent.main_child = Some(node_index);
                        if parent.halfmove > current_move_number {
                            return Err(PgnMoveTextParseError::IncoherentMoveNumbering {
                                expected: parent.halfmove,
                                got: current_move_number,
                            });
                        } else if parent.halfmove == current_move_number {
                            current_move_number = parent.halfmove + 1;
                        }
                    } else if let Some(&Some(parent_index)) = current_node_stack.last() {
                        let parent = result.get_move_mut(parent_index);
                        parent.ravs.push(node_index);
                        if parent.halfmove > current_move_number {
                            return Err(PgnMoveTextParseError::IncoherentMoveNumbering {
                                expected: parent.halfmove,
                                got: current_move_number,
                            });
                        }
                    }
                    result.get_move_mut(node_index).halfmove = current_move_number;
                    current_node_stack.push(Some(node_index));
                }
                None => return Err(PgnMoveTextParseError::MissingGameResult)?,
            }
        }
        Ok((result, s))
    }
}
impl std::fmt::Display for PgnMoveText {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Keeps track of line length, export format limits this to 80.
        let mut line_buffer: heapless::String<80> = heapless::String::new();
        fn write_or_flush(
            f: &mut std::fmt::Formatter<'_>,
            args: Arguments,
            line_buffer: &mut heapless::String<80>,
        ) -> std::fmt::Result {
            let prev_line_buff = line_buffer.clone();
            if line_buffer.write_fmt(args).is_err() {
                writeln!(f, "{prev_line_buff}")?;
                line_buffer.clear();
                line_buffer.write_fmt(args).unwrap()
            }
            Ok(())
        }

        let mut to_visit = vec![(0, false, false)];
        let mut rav_depth = 0;
        while let Some((node, rav_start, force_move_num)) = to_visit.pop() {
            if rav_start {
                rav_depth += 1;
                write_or_flush(f, format_args!("("), &mut line_buffer)?;
            }
            if self.moves[node].white_to_play() {
                write_or_flush(
                    f,
                    format_args!("{}.", self.moves[node].fullmove()),
                    &mut line_buffer,
                )?;
            } else if force_move_num {
                write_or_flush(
                    f,
                    format_args!("{}...", self.moves[node].fullmove()),
                    &mut line_buffer,
                )?;
            }
            write_or_flush(f, format_args!("{}", self.moves[node].mv), &mut line_buffer)?;
            if self.moves[node].nag != 0 {
                write_or_flush(
                    f,
                    format_args!(" ${}", self.moves[node].nag),
                    &mut line_buffer,
                )?;
            }
            match self.moves[node].main_child {
                Some(c) => {
                    to_visit.push((
                        c,
                        false,
                        self.moves[node].nag != 0 || !self.moves[node].ravs.is_empty(),
                    ));
                    write_or_flush(f, format_args!(" "), &mut line_buffer)?;
                }
                None => {
                    if rav_depth != 0 {
                        rav_depth -= 1;
                        write_or_flush(f, format_args!(") "), &mut line_buffer)?;
                    }
                }
            }
            for &rav in self.moves[node].ravs.iter().rev() {
                to_visit.push((rav, true, self.moves[node].nag != 0))
            }
        }
        write_or_flush(
            f,
            format_args!(
                " {}",
                match self.result {
                    None => "*",
                    Some(GameResult::Checkmate(Colour::White)) => "0-1",
                    Some(GameResult::Checkmate(Colour::Black)) => "1-0",
                    Some(GameResult::Draw(_)) => "1/2-1/2",
                }
            ),
            &mut line_buffer,
        )?;
        write!(f, "{line_buffer}")
    }
}

/// Represents a fully recorded PGN game, with contextual tags, moves played in order,
/// as well as annotations.
///
/// Tag pairs are ordered as indicated by the PGN standard: the seven tag roster appears
/// first in a fixed order, then additionnal tags in lexicographic order.
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash, Default)]
pub struct PgnGame {
    tags: Vec<PgnTagPair>,
    movetext: PgnMoveText,
}
#[derive(Debug, Clone, Copy, Error, PartialEq, Eq, Hash)]
pub enum PgnGameParseError {
    #[error(transparent)]
    TagPairsError(#[from] PgnTagPairParseError),
    #[error(transparent)]
    MovetextError(#[from] PgnMoveTextParseError),
}
impl PartialFromStr for PgnGame {
    type Err = PgnGameParseError;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        let (tags, s) = parse_tag_pairs(s)?;
        let (movetext, s) = PgnMoveText::partial_from_str(s)?;
        Ok((Self { tags, movetext }, s))
    }
}
impl std::fmt::Display for PgnGame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for tag_pair in &self.tags {
            writeln!(f, "{tag_pair}")?
        }
        writeln!(f)?;
        write!(f, "{}", self.movetext)?;
        Ok(())
    }
}
