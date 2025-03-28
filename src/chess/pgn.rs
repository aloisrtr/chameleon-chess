//! # Portable Game Notation standard implementation
//! The implementation follows the 2023-03-22 revision of the PGN standard which
//! can be found [here](https://github.com/fsmosca/PGN-Standard/blob/master/PGN-Standard.txt).

use std::{ascii::AsciiExt, str::FromStr};

use super::{action::SanMove, colour::Colour};

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
            (Some(_), None) => std::cmp::Ordering::Greater,
            (None, Some(_)) => std::cmp::Ordering::Less,
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
impl std::fmt::Display for PgnTagPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{} \"{}\"]", self.tag, self.value)
    }
}

/// Represents a single move and any number of following moves within a PGN movetext
/// section.
pub struct PgnMoveTextNode {
    fullmove: u16,
    mv: SanMove,
    nag: u8,
    main_child: Option<usize>,
    ravs: Vec<usize>,
}

/// Movetext structure with support for RAV (variations) and NAG (annotations).
///
/// It is represented as a tree of [`PgnMoveTextNode`]s.
#[derive(Default)]
pub struct PgnMoveText {
    moves: Vec<PgnMoveTextNode>,
}
impl PgnMoveText {
    pub fn add_move(&mut self, mv: SanMove) -> usize {
        self.moves.push(PgnMoveTextNode {
            fullmove: 0,
            mv,
            nag: 0,
            main_child: None,
            ravs: vec![],
        });
        self.moves.len() - 1
    }

    pub fn get_move_info(&self, index: usize) -> &PgnMoveTextNode {
        &self.moves[index]
    }

    pub fn get_move_info_mut(&mut self, index: usize) -> &mut PgnMoveTextNode {
        &mut self.moves[index]
    }
}
impl std::fmt::Display for PgnMoveText {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut to_visit = vec![(0, false)];
        let mut rav_depth = 0;
        while let Some((node, rav_start)) = to_visit.pop() {
            if rav_start {
                rav_depth += 1;
                write!(f, "( ")?;
            }
            write!(f, "{} ", self.moves[node].mv)?;
            match self.moves[node].main_child {
                Some(c) => to_visit.push((c, false)),
                None => {
                    if rav_depth != 0 {
                        rav_depth -= 1;
                        write!(f, ") ")?;
                    }
                }
            }
            for &rav in self.moves[node].ravs.iter().rev() {
                to_visit.push((rav, true))
            }
        }
        Ok(())
    }
}

/// Represents a fully recorded PGN game, with contextual tags, moves played in order,
/// as well as annotations.
///
/// Tag pairs are ordered as indicated by the PGN standard: the seven tag roster appears
/// first in a fixed order, then additionnal tags in lexicographic order.
pub struct PgnGame {
    tags: Vec<PgnTagPair>,
    movetext: PgnMoveText,
}
impl std::fmt::Display for PgnGame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for tag_pair in &self.tags {
            writeln!(f, "{tag_pair}")?
        }
        writeln!(f)?;

        Ok(())
    }
}

// PARSING UTILITIES
// We use parser combinators here.

/// Returns the rest of the input after walking a comment.
fn walk_whitespace_and_comments(mut src: &str) -> &str {
    loop {
        match src.chars().next() {
            Some('{') => {
                // Continue until we reach }
                let (_, left) = src.split_once('}').unwrap();
                src = left
            }
            Some(';') => {
                // Continue until end of line or EOF.
                let (_, left) = src.split_once('\n').unwrap();
                src = left
            }
            Some(c) if c.is_whitespace() => {
                src = src.trim_start();
            }
            _ => return src,
        }
    }
}

fn parse_string(src: &str) -> Result<(&str, String), ()> {
    let mut result = String::new();
    let mut chars = src.chars();

    match chars.next() {
        Some('"') => (),
        _ => return Err(()),
    }

    let mut escaped = false;
    let mut escaped_count = 0;
    while let Some(c) = chars.next() {
        match c {
            '"' if !escaped => break,
            '\\' if !escaped => escaped = true,
            '\t' => return Err(()),
            _ => {
                result.push(c);
                if escaped {
                    escaped_count += 1;
                    escaped = false
                }
            }
        }
    }

    Ok((&src[result.len() + 2 + escaped_count..], result))
}

fn parse_int(src: &str) -> Result<(&str, u16), ()> {
    let mut result = 0u16;
    let mut parsed = 0;
    for c in src.chars() {
        if let Some(digit) = c.to_digit(10) {
            result = result * 10 + digit as u16;
            parsed += 1
        }
    }

    if parsed != 0 {
        Ok((&src[parsed..], result))
    } else {
        Err(())
    }
}

fn parse_symbol(src: &str) -> Result<(&str, String), &str> {
    todo!()
}

fn parse_san_move(src: &str) -> Result<(&str, SanMove), ()> {
    todo!()
}

fn parse_tag(src: &str) -> Result<(&str, String), ()> {
    let mut result = String::new();
    let mut chars = src.chars();

    match chars.next() {
        Some(c) if c.is_alphanumeric() => result.push(c),
        _ => return Err(()),
    }

    while let Some(c) = chars.next() {
        if c.is_alphanumeric() || c == '_' {
            result.push(c)
        } else if c == ' ' {
            break;
        } else {
            return Err(());
        }
    }

    Ok((&src[result.len()..], result))
}

fn parse_tag_pair(s: &str) -> Result<(&str, PgnTagPair), ()> {
    let s = walk_whitespace_and_comments(s);
    if let Some('[') = s.chars().next() {
        let left = walk_whitespace_and_comments(&s[1..]);
        let Ok((left, tag)) = parse_tag(left) else {
            return Err(());
        };
        let left = walk_whitespace_and_comments(left);
        let Ok((left, value)) = parse_string(left) else {
            return Err(());
        };
        let left = walk_whitespace_and_comments(left);
        if let Some(']') = left.chars().next() {
            Ok((&left[1..], PgnTagPair { tag, value }))
        } else {
            Err(())
        }
    } else {
        Err(())
    }
}

fn parse_tag_pairs(mut s: &str) -> Result<(&str, Vec<PgnTagPair>), ()> {
    let mut result = vec![];
    while let Ok((left, tagpair)) = parse_tag_pair(s) {
        s = walk_whitespace_and_comments(left);
        result.push(tagpair);
    }
    Ok((s, result))
}

fn parse_movetext(mut s: &str) -> Result<(&str, PgnMoveText), ()> {
    let mut result = PgnMoveText::default();
    let mut current_node_stack = vec![];
    let mut current_move_number = 1;
    loop {
        s = walk_whitespace_and_comments(s);
        if let Ok((left, move_num)) = parse_int(s) {
            s = left;
            current_move_number = move_num
        } else if let Ok((left, san_move)) = parse_san_move(s) {
            s = left;
            let node_index = result.add_move(san_move);
            result.get_move_info_mut(node_index).fullmove = current_move_number;
            if let Some(parent_index) = current_node_stack.pop() {
                let parent = result.get_move_info_mut(parent_index);
                parent.main_child = Some(node_index);
                if parent.fullmove > current_move_number {
                    // TODO: Error incoherent move numbering
                    return Err(());
                }
            }
        } else if s.chars().next() != Some('.') {
            break;
        }
        // TODO: support for RAVs and NAGs
    }
    Ok((s, result))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn walk_eol_comment() {
        assert_eq!(
            walk_whitespace_and_comments(";fnzjnfzkjnef\nhello"),
            "hello"
        )
    }

    #[test]
    fn walk_embedded_comment() {
        assert_eq!(walk_whitespace_and_comments("{fnzjnfzkjnef}hello"), "hello");
        assert_eq!(
            walk_whitespace_and_comments("{fnzjnf}zkjnef}hello"),
            "zkjnef}hello"
        )
    }

    #[test]
    fn walk_whitespace_works() {
        assert_eq!(walk_whitespace_and_comments("      \n\n\t  hey"), "hey")
    }
    #[test]
    fn walk_whitespace_and_comments_both() {
        assert_eq!(
            walk_whitespace_and_comments("{comment}      \n;other line comment\n\t  hey"),
            "hey"
        )
    }

    #[test]
    fn parse_tag_ok() {
        assert_eq!(
            parse_tag("Event and other stuff"),
            Ok((" and other stuff", "Event".to_string()))
        );
        assert!(parse_tag("Even-t and other stuff").is_err());
        assert_eq!(
            parse_tag("Even_t and other stuff"),
            Ok((" and other stuff", "Even_t".to_string()))
        );
        assert_eq!(
            parse_tag("Even1_t and other stuff"),
            Ok((" and other stuff", "Even1_t".to_string()))
        );
        assert_eq!(
            parse_tag("23Event and other stuff"),
            Ok((" and other stuff", "23Event".to_string()))
        );
        assert!(parse_tag("_vent and other stuff").is_err());
    }

    #[test]
    fn parse_string_ok() {
        assert_eq!(
            parse_string(r#""hello i am a string""#),
            Ok(("", "hello i am a string".to_string()))
        );
        assert_eq!(
            parse_string(r#""hello i am \"escaped\"""#),
            Ok(("", "hello i am \"escaped\"".to_string()))
        );
        assert_eq!(
            parse_string(r#""hello i am \\ antislash""#),
            Ok(("", "hello i am \\ antislash".to_string()))
        );
    }

    #[test]
    fn parse_tag_pair_ok() {
        assert_eq!(
            parse_tag_pair("[ Event  \"World chess championship\"  ]\n ..."),
            Ok((
                "\n ...",
                PgnTagPair {
                    tag: "Event".to_string(),
                    value: "World chess championship".to_string()
                }
            ))
        )
    }

    #[test]
    fn parse_tag_pairs_ok() {
        let input = r#"
            [Event "World chess championship"][Date "YYYY.MM.DD"] [RandomTag 
            "Finished newline"]

            [Forgot_this "Sad"]
        "#;
        let (_, tags) = parse_tag_pairs(input).unwrap();
        assert_eq!(
            &tags,
            &[
                PgnTagPair {
                    tag: "Event".to_string(),
                    value: "World chess championship".into()
                },
                PgnTagPair {
                    tag: "Date".into(),
                    value: "YYYY.MM.DD".into()
                },
                PgnTagPair {
                    tag: "RandomTag".into(),
                    value: "Finished newline".into()
                },
                PgnTagPair {
                    tag: "Forgot_this".into(),
                    value: "Sad".into()
                }
            ]
        )
    }
}
