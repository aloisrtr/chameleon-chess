![Horsey logo](assets/logo.svg)

# Horsey
A complete and powerful Chess library and engine written from the ground up.

## Features
- Efficient bitboard-based board representation and move generation routines.
- [UCI protocol](https://www.wbec-ridderkerk.nl/html/UCIProtocol.html) support (both client and server).

## TODO
- Highly parallel search routines to take advantage of modern hardware.
- Support for endgame tablebases.
- Monte-Carlo Tree Search (RAVE + UCT) and Alpha-Beta search routines.
- Depth-First Proof-Number Search for checkmate search.
- Value and policy network using NNUE architecture for fast inference on modern CPUs.
- Library bindings for other languages (Python, C/C++, Java, etc)

## Engine
By default, running the engine with no arguments runs the UCI mode. In this state,
the engine is able to interact with UCI GUIs or by inputting commands manually in
the terminal.

> If the program detects that it is being run within a terminal, additionnal commands
> and a full REPL experience are available for ease of interaction.


### Perft
The engine can run a [Perft test](https://www.chessprogramming.org/Perft) for benchmarking
or testing purposes. For a full list of flags, run:
```
horsey perft --help
```
This requires compiling the engine with the `perft` feature flag.

### Library
Full access to the engine's power is available through its Rust crate. The crate
is divided in multiple segments:
- `game` contains the core Chess API. Interacting with positions, moves or pieces is done through the types defined in this module.
- `search` grants access to the various search routines implemented by Horsey with full configuration, async/parallel/blocking routines and more.
- `uci` contains everything needed for UCI compatibility, both from a client and server perspective.
- `brain` is used to access Horsey's value and policy networks, self-play and training routines.

Full documentation for the library is available [here]()

