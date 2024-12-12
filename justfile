validate_perft:
    cargo test perft -- --include-ignored

test:
    cargo test

flamegraph:
    CARGO_PROFILE_RELEASE_DEBUG=true cargo flamegraph -- perft 7 -dbi --no-board

run:
    cargo run

run_release:
    cargo run --release

build:
    cargo build

release:
    cargo build --release

release_native:
    RUSTFLAGS="-C target-cpu=native" cargo build --release
