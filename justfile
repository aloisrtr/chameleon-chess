validate-perft:
    cargo test perft -- --include-ignored

test:
    cargo test

flamegraph:
    RUSTFLAGS="-C target-cpu=native" CARGO_PROFILE_RELEASE_DEBUG=true cargo flamegraph -- perft 7 -dbi --no-board

run:
    cargo run

run-release:
    cargo run --release

build:
    cargo build

release:
    cargo build --release

release-native:
    RUSTFLAGS="-C target-cpu=native" cargo build --release
