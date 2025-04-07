//! Helper functions for parsing PGN

use super::*;

/// Returns the rest of the input after walking a comment.
pub fn walk_whitespace_and_comments(mut src: &str) -> &str {
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

pub fn parse_game_result(src: &str) -> Result<(Option<GameResult>, &str), ()> {
    let is_prefix = |s: &str, pre: &str| s.len() >= pre.len() && &s[..pre.len()] == pre;
    if is_prefix(src, "1/2-1/2") {
        Ok((
            // TODO: not necessarilly always an agreed draw
            Some(GameResult::Draw(DrawKind::Agreement)),
            &src["1/2-1/2".len()..],
        ))
    } else if is_prefix(src, "1-0") {
        Ok((
            Some(GameResult::Checkmate(Colour::Black)),
            &src["1-0".len()..],
        ))
    } else if is_prefix(src, "0-1") {
        Ok((
            Some(GameResult::Checkmate(Colour::White)),
            &src["0-1".len()..],
        ))
    } else if is_prefix(src, "*") {
        Ok((None, &src["*".len()..]))
    } else {
        Err(())
    }
}

/// Parses valid PGN tags.
pub fn parse_tag(src: &str) -> Result<(String, &str), ()> {
    let mut result = String::new();
    let mut chars = src.chars();

    match chars.next() {
        Some(c) if c.is_alphanumeric() => result.push(c),
        _ => return Err(()),
    }

    for c in chars {
        if c.is_alphanumeric() || c == '_' {
            result.push(c)
        } else if c == ' ' {
            break;
        } else {
            return Err(());
        }
    }

    let left = &src[result.len()..];
    Ok((result, left))
}

/// Parses a vector of PGN tag pairs, separated by zero or more whitespaces.
pub fn parse_tag_pairs(mut s: &str) -> Result<(Vec<PgnTagPair>, &str), PgnTagPairParseError> {
    s = walk_whitespace_and_comments(s);
    let mut result = vec![];
    while let Ok((tagpair, left)) = PgnTagPair::partial_from_str(s) {
        s = walk_whitespace_and_comments(left);
        result.push(tagpair);
    }
    result.sort();
    Ok((result, s))
}

#[cfg(test)]
mod test {
    use crate::parsing::parse_string;

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
            Ok(("Event".to_string(), " and other stuff"))
        );
        assert!(parse_tag("Even-t and other stuff").is_err());
        assert_eq!(
            parse_tag("Even_t and other stuff"),
            Ok(("Even_t".to_string(), " and other stuff"))
        );
        assert_eq!(
            parse_tag("Even1_t and other stuff"),
            Ok(("Even1_t".to_string(), " and other stuff"))
        );
        assert_eq!(
            parse_tag("23Event and other stuff"),
            Ok(("23Event".to_string(), " and other stuff"))
        );
        assert!(parse_tag("_vent and other stuff").is_err());
    }

    #[test]
    fn parse_string_ok() {
        assert_eq!(
            parse_string(r#""hello i am a string""#),
            Ok(("hello i am a string".to_string(), ""))
        );
        assert_eq!(
            parse_string(r#""hello i am \"escaped\"""#),
            Ok(("hello i am \"escaped\"".to_string(), ""))
        );
        assert_eq!(
            parse_string(r#""hello i am \\ antislash""#),
            Ok(("hello i am \\ antislash".to_string(), ""))
        );
    }

    #[test]
    fn parse_tag_pair_ok() {
        assert_eq!(
            PgnTagPair::partial_from_str("[ Event  \"World chess championship\"  ]\n ..."),
            Ok((
                PgnTagPair {
                    tag: "Event".to_string(),
                    value: "World chess championship".to_string()
                },
                "\n ...",
            ))
        )
    }

    #[test]
    fn parse_tag_pairs_ok() {
        let input = r#"
            [Event "World chess championship"][RandomTag "Finished newline"] [Date 
            "2025.09.12"]

            [Forgot_this "Sad"]
        "#;
        let (tags, _) = parse_tag_pairs(input).unwrap();
        assert_eq!(&tags, &[
            PgnTagPair {
                tag: "Event".to_string(),
                value: "World chess championship".into()
            },
            PgnTagPair {
                tag: "Date".into(),
                value: "2025.09.12".into()
            },
            PgnTagPair {
                tag: "Forgot_this".into(),
                value: "Sad".into()
            },
            PgnTagPair {
                tag: "RandomTag".into(),
                value: "Finished newline".into()
            },
        ])
    }

    #[test]
    fn parse_movetext_plain() {
        let input = r#"
            1.e4 e5 2.Nf3 Nc6 3.Bb5 {This opening is called the Ruy Lopez.} 3...a6
            4.Ba4 Nf6 5.O-O Be7 *
        "#;
        let expected = "1.e4 e5 2.Nf3 Nc6 3.Bb5 a6 4.Ba4 Nf6 5.O-O Be7 *";
        match PgnMoveText::partial_from_str(input) {
            Ok((movetext, _)) => {
                assert_eq!(format!("{movetext}").trim(), expected)
            }
            Err(e) => panic!("Parsing failed: {e:?}"),
        }
    }

    #[test]
    fn parse_movetext_nag() {
        let input = r#"
            1.e4 e5 2.Nf3 $23 Nc6 3.Bb5 {This opening is called the Ruy Lopez.} 3...a6
            4.Ba4 Nf6 5.O-O Be7 *
        "#;
        let expected = "1.e4 e5 2.Nf3 $23 2...Nc6 3.Bb5 a6 4.Ba4 Nf6 5.O-O Be7 *";
        match PgnMoveText::partial_from_str(input) {
            Ok((movetext, _)) => {
                assert_eq!(format!("{movetext}").trim(), expected)
            }
            Err(e) => panic!("Parsing failed: {e:?}"),
        }
    }

    #[test]
    fn parse_movetext_rav() {
        let input = r#"
            1.e4 e5 2.Nf3 (Nb3 Nc6 3.Bc4) 2...Nc6 3.Bb5 {This opening is called the Ruy Lopez.} 3...a6
            4.Ba4 Nf6 5.O-O Be7 *
        "#;
        let expected = "1.e4 e5 2.Nf3 (2.Nb3 Nc6 3.Bc4) 2...Nc6 3.Bb5 a6 4.Ba4 Nf6 5.O-O Be7 *";
        match PgnMoveText::partial_from_str(input) {
            Ok((movetext, _)) => {
                assert_eq!(format!("{movetext}").trim(), expected)
            }
            Err(e) => panic!("Parsing failed: {e:?}"),
        }
    }

    #[test]
    fn parse_movetext_rav_multiple() {
        let input = r#"
            1.e4 e5 2.Nf3 (Nb3 Nc6 3.Bc4) (d4 Nc6) 2...Nc6 3.Bb5 {This opening is called the Ruy Lopez.} 3...a6
            4.Ba4 Nf6 5.O-O Be7 *
        "#;
        let expected =
            "1.e4 e5 2.Nf3 (2.Nb3 Nc6 3.Bc4) (2.d4 Nc6) 2...Nc6 3.Bb5 a6 4.Ba4 Nf6 5.O-O Be7\n *";
        match PgnMoveText::partial_from_str(input) {
            Ok((movetext, _)) => {
                assert_eq!(format!("{movetext}").trim(), expected)
            }
            Err(e) => panic!("Parsing failed: {e:?}"),
        }
    }

    #[test]
    fn parse_movetext_rav_nested() {
        let input = r#"
            1.e4 e5 2.Nf3 (Nb3 (d4 Na6) Nc6 3.Bc4) 2...Nc6 3.Bb5 {This opening is called the Ruy Lopez.} 3...a6
            4.Ba4 Nf6 5.O-O Be7 *
        "#;
        let expected = "1.e4 e5 2.Nf3 (2.Nb3 (2.d4 Na6) 2...Nc6 3.Bc4) 2...Nc6 3.Bb5 a6 4.Ba4 Nf6 5.O-O \nBe7 *";
        match PgnMoveText::partial_from_str(input) {
            Ok((movetext, _)) => {
                assert_eq!(format!("{movetext}").trim(), expected)
            }
            Err(e) => panic!("Parsing failed: {e:?}"),
        }
    }

    #[test]
    fn parse_full_pgn_game() {
        let input = r#"
[Event "F/S Return Match"]
[Site "Belgrade, Serbia JUG"]
[Date "1992.11.04"]
[Round "29"]
[White "Fischer, Robert J."]
[Black "Spassky, Boris V."]
[Result "1/2-1/2"]

1.e4 e5 2.Nf3 Nc6 3.Bb5 {This opening is called the Ruy Lopez.} 3...a6
4.Ba4 Nf6 5.O-O Be7 6.Re1 b5 7.Bb3 d6 8.c3 O-O 9.h3 Nb8 10.d4 Nbd7
11.c4 c6 12.cxb5 axb5 13.Nc3 Bb7 14.Bg5 b4 15.Nb1 h6 16.Bh4 c5 17.dxe5
Nxe4 18.Bxe7 Qxe7 19.exd6 Qf6 20.Nbd2 Nxd6 21.Nc4 Nxc4 22.Bxc4 Nb6
23.Ne5 Rae8 24.Bxf7+ Rxf7 25.Nxf7 Rxe1+ 26.Qxe1 Kxf7 27.Qe3 Qg5 28.Qxg5
hxg5 29.b3 Ke6 30.a3 Kd6 31.axb4 cxb4 32.Ra5 Nd5 33.f3 Bc8 34.Kf2 Bf5
35.Ra7 g6 36.Ra6+ Kc5 37.Ke1 Nf4 38.g3 Nxh3 39.Kd2 Kb5 40.Rd6 Kc5 41.Ra6
Nf2 42.g4 Bd3 43.Re6 1/2-1/2            
         "#;

        let expected = r#"
[Event "F/S Return Match"]
[Site "Belgrade, Serbia JUG"]
[Date "1992.11.04"]
[Round "29"]
[White "Fischer, Robert J."]
[Black "Spassky, Boris V."]
[Result "1/2-1/2"]

1.e4 e5 2.Nf3 Nc6 3.Bb5 a6 4.Ba4 Nf6 5.O-O Be7 6.Re1 b5 7.Bb3 d6 8.c3 O-O 9.h3 
Nb8 10.d4 Nbd7 11.c4 c6 12.cxb5 axb5 13.Nc3 Bb7 14.Bg5 b4 15.Nb1 h6 16.Bh4 c5 
17.dxe5 Nxe4 18.Bxe7 Qxe7 19.exd6 Qf6 20.Nbd2 Nxd6 21.Nc4 Nxc4 22.Bxc4 Nb6 23.
Ne5 Rae8 24.Bxf7+ Rxf7 25.Nxf7 Rxe1+ 26.Qxe1 Kxf7 27.Qe3 Qg5 28.Qxg5 hxg5 29.b3 
Ke6 30.a3 Kd6 31.axb4 cxb4 32.Ra5 Nd5 33.f3 Bc8 34.Kf2 Bf5 35.Ra7 g6 36.Ra6+ Kc5
 37.Ke1 Nf4 38.g3 Nxh3 39.Kd2 Kb5 40.Rd6 Kc5 41.Ra6 Nf2 42.g4 Bd3 43.Re6 1/2-1/2
         "#;
        match PgnGame::partial_from_str(input) {
            Ok((game, _)) => {
                println!("{game:?}");
                assert_eq!(format!("{game}").trim(), expected.trim())
            }
            Err(e) => panic!("Parsing failed: {e:?}"),
        }
    }
}
