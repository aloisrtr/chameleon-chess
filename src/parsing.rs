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
