# Horsey: library
A chess library that aims to be:
- **correct**: move generation and move making and parsing should be not raise any erronous behavior.
- **fully-featured**: most of what you'd want from a chess library can be found here (PGN/EPD/FEN parsing, all sorts of move encodings, multiple search algorithms, UCI client/server implementations)
- **efficient**: `unsafe` alternatives when you're sure of what you are doing, safe subset as efficient as can be
- **small**: low dependencies, `feature`-gating for non-essential features

## Features
By default, only the core library (board representation) is available. You can pick
and chose multiple complementary features if you need them.
- `uci-client`: makes available the UCI client code.
- `uci-server`: makes available the UCI server code.
- `pgn`: enables PGN representation and parsing under the `pgn` module.
- `epd`: enables EPD representation and parsing under the `epd` module.
- `log`: enables logging facilities through the [`log`](https://docs.rs/log/latest/log/) crate.
- `serde`: enables serialization/deserialization of various data structures through the [`serde`](https://serde.rs/) crate.

## TODO before a first release
There's a loooot left to do before this can be released in a satisfactory state.
- **remove standard library dependency**: this library does not need `std`. It should be made `#![no-std]`, without much friction.
- **search algorithms**: alpha-beta, MCTS and PNS are to be implemented.
- **clean up of some of the code**: Some code has been written a while ago. Clippy lints, decoupling, etc are to be dealt with in order for the library to be as clean as possible.


