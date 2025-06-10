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

> Note that the core implementation may still be implemented in a way that facilitates
> other module's implementations. An example of this is Zobrist hashing, a part of the
> core `chess` module, which is modeled to match PolyGlot position keys.
>
> This does not hinder or change anything for someone that only uses the `chess` module,
> but avoids an entire file of mostly duplicated code.

On top of that, the library has no default features. We can't define a set of features
that "everyone will likely want to have", except for "basic chess representation"
(otherwise why depend on this library?)

### Protocols and formats
Protocols and formats implement tools that are able to parse a "unit" for such
formats (games for PGN, positions for EPD, entries for PolyGlot opening books, etc).

It is outside of the scope of the library to implement functionnality such as "probing PolyGlot books"
or "loading PGN files". This has a few advantages:
- implementers are free to handle IO however they want, including different `async` runtimes
- the internal representation within the final software can be modelled in an "optimal" way for this specific software

As such, the boundary of what Horsey should handle is "parse the source", but not "provide the source".

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
Text format opening books (PGN or EPD) are supported (see section above).

The PolyGlot format is also supported by granting functionnality for parsing/writing entries
from/to a slice of bytes. This should allow it to work with sources that pull data from


### Endgame tablebases
We'll see about those later, I still need to research the probing code more in depth.

## Protocols
Currently, only UCI is supported. This is more of a time problem than a willing decision,
and I'm not against implementing other protocols if need be.

It should be noted that (as far as I know), UCI is the only non-obsolete protocol
out there.

Protocol implementations simply define the *structure* of the exchange, not the
medium. This should provide maximum flexibility to implementers, at the cost of
a little more code to write.
