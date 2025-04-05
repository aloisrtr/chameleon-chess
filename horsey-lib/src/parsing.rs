//! # Parsing
//! Chess has made available a bunch of formats for moves, positions, or entire games.
//!
//! Horsey makes these parsable from raw strings using the standard Rust [`FromStr`](std::str::FromStr)
//! trait.
//!
//! On top of that, all parsable types implement the [`PartialFromStr`] trait. This
//! trait implements *parser combinators*.
//!
//! Unlike [`FromStr`], the `Ok` variant returned by [`PartialFromStr`] contains two
//! values:
//! - The parsed value
//! - A suffix of the input that was not part of the parsed value.
//! A string like "d4rest" would return `Ok(Square::D4, "rest")` when parsed.
//!
//! Using this parsing scheme allows the combination of parsers over a large input
//! string more easily. For example, the string "d4d5h2" can be parsed into three
//! squares by successive calls to `partial_from_str`.

use std::convert::Infallible;

pub trait PartialFromStr: Sized {
    type Err;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err>;
}
impl<T: PartialFromStr> PartialFromStr for Option<T> {
    type Err = Infallible;

    fn partial_from_str(s: &str) -> Result<(Self, &str), Self::Err> {
        match T::partial_from_str(s) {
            Ok((value, rest)) => Ok((Some(value), rest)),
            Err(_) => Ok((None, s)),
        }
    }
}
impl<T: PartialFromStr> PartialFromStr for Result<T, <T as PartialFromStr>::Err> {
    type Err = Infallible;

    fn partial_from_str(s: &str) -> Result<(Self, &str), <Self as PartialFromStr>::Err> {
        match T::partial_from_str(s) {
            Ok((value, rest)) => Ok((Ok(value), rest)),
            Err(e) => Ok((Err(e), s)),
        }
    }
}

/// Parses a string value with escaped characters.
pub(crate) fn parse_string(src: &str) -> Result<(String, &str), ()> {
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

    let left = &src[result.len() + 2 + escaped_count..];
    Ok((result, left))
}

/// Parses a a u16 value.
pub(crate) fn parse_int(src: &str) -> Result<(u16, &str), ()> {
    let mut result = 0u16;
    let mut parsed = 0;
    for c in src.chars() {
        if let Some(digit) = c.to_digit(10) {
            result = result * 10 + digit as u16;
            parsed += 1
        } else {
            break;
        }
    }

    if parsed != 0 {
        Ok((result, &src[parsed..]))
    } else {
        Err(())
    }
}

/// Returns the rest of the input after walking whitespace values.
pub fn walk_whitespace(src: &str) -> &str {
    src.trim_start()
}
