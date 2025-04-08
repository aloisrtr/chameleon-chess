# Making modifications to the code
(This is a document mainly targetted at... myself, just some guidelines to stick to)

## Benchmarking
All benchmarks use the Criterion crate, and can run for a while (especially perft benches).

While not necessary, it would be good to check the difference between a native build
(with all CPU features, `RUSTFLAGS=-C target-cpu=native`) and a generic build
once in a while to make sure that the differences are not tooo huge.

## Modularity
As a rule of thumb: *only* the `chess` module should not be feature-gated. It implements
all that's ever needed to represent and play a game of chess.

Any other module should be optional and therefore feature-gated. As such, the `chess`
module cannot depend on anything that is defined outside of it.

> The only exception to this is the update of NNUE features. Since the only place this
> can be done incrementally is within the `make` and `unmake` functions, we have to
> feature-gate a bunch of expressions in there to make it work while keeping everything modular.
>
> Given how optional NNUE is to library implementers, this seems like a small price to pay.

On top of that, the library has no default features. We can't define a set of features
that "everyone will likely want to have".

### Dependencies
Dependencies should be kept to an absolute minimum. Two dependencies are currently needed:
- `rand` for zobrist hashing and simulation in MCTS
- `heapless` for stack-stored data structures (notably the list of generated moves)
- `num_cpus` for UCI options (optional, only added when UCI code is active)

On top of that, as long as crates.io doesn't have some form of quality control,
added dependencies need to be thoroughly checked, and added if and only if the required
code cannot be reimplemented cleanly and/or more efficiently within the engine.

As an example, `thiserror` just automates the implementations of `From`, `Error` and
`Display` for error types, at the cost of way longer compile times due to macros + 1 dependency.
This is not a valid tradeoff.

Opposed to that are the `serde` and `log` crates, which are "standards". Reimplementing
them would just create more friction when interacting with other crates, however
they should still be left as features for implementers that do not require them.

## Board representation (`chess` module)
The board representation has to prioritize (in order):
- correctness
- efficiency ~= readability

Every new change, even small, should follow the process of:
+ running the `movegen` benchmark before
+ making changes
+ running perft tests (if any fails, repeat step 2)
+ running the `movegen` benchmark with changes
  - if performance has regressed, either go back to step 2 or roll back
  - otherwise, we're good!

On top of that, there are a few API designs that need to stick:
- all move representations should implement the `ChessMove` trait to be usable by the `Position` structure.
- the `Position` structure should implement `From` for each game description format (FEN, EPD, PGN, etc).

### General stuff
- If a function or anything can be made `const`, do it.
- Small functions, or with a single call site, should be hinted with `#[inline]`.

### Bitboards
Bitboards are the core structure behind the board representation: **it needs to be correct and fast**.

If some intrinsic is available to make any operation faster, it should be used and
guarded by a `#[cfg(...)]` macro (see `pext` and `pdep` for examples).

All function should be hinted with `#[inline]` by default, unless there is a strong
case for avoiding this.

As it stands, the `Bitboard` structure is feature-complete, and should not receive
much changes.

### Magic bitboards
Sliding pieces moves (bishop, rook and queen) are computed using magic bitboards. The
current implementation follows the mainstream "fancy" magic bitboards, with tables
computed at compile-time and stored within the binary.

While compile-time computation is probably the way to go from benchmarking, any other
implementation for magic bitboards is welcome (PEXT bitboards for CPUs that support it,
or black magic bitboards).

### Actions
This encodes anything that represents a chess move. If some new move representation
pops up, make sure it:
- implements `ChessMove` to be used with `Position`
- implements `PartialFromStr` and `FromStr`, using other parsers for squares, pieces etc.

## Formats
### Games
Chess formats (such as PGN and EPD currently) should be able to parse from files
one game at a time. This is easily done by implementing `PartialFromStr` and using
it with a `BuffReader` implementation.

The speed of such parsers is important, but less than their readability.

`async` is **not** this library's concern *currently*. The parsing code can likely
be encapsulated within asynchronous functions, but it's the job of IO libraries to
provide that functionnality, not the parser's.

### Opening books
Opening data is stored as a game tree with WDL values. The best move can easily be queried
from a node by scanning its children, and it's a rather efficient representation.

As of now, only text format opening books (PGN or EPD) are supported. The PolyGlot
format should be supported in the near future.

### Endgame tablebases
We'll see about those later, I still need to research the probing code more in depth.

## Protocols
Currently, only UCI is supported. This is more of a time problem than a willing decision,
and I'm not against implementing other protocols if need be.

It should be noted that (as far as I know), UCI is the only non-obsolete protocol
out there.

Protocols should work over *anything* that implements reader/writer functionnality. While
not a base goal of UCI (it specifies stdin/stdout as channels), this is pretty easy
to work with in Rust with generics and adds waaay more freedom to implementers. Want
to talk UCI over a network? Done. Over SPI? Sure. You get the point.

### Async
Protocols could implement async counterparts, since they technically read/write directly
instead of just parsing, and that's where the barrier lies. This is not implemented
currently, but planned. Synchronous variants should still take priority.
