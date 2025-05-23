use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use horsey::chess::{fen::Fen, perft::perft};

const PERFT_POS: [(&str, u8); 7] = [
    (
        "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1",
        5,
    ),
    (
        "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1",
        5,
    ),
    ("8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 7),
    (
        "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1",
        5,
    ),
    (
        "r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ - 0 1",
        5,
    ),
    (
        "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8",
        5,
    ),
    (
        "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10",
        5,
    ),
];

fn perft_bench(c: &mut Criterion) {
    let mut group = c.benchmark_group("movegen");
    for (fen, depth) in PERFT_POS {
        group.bench_with_input(
            BenchmarkId::from_parameter(fen.split_whitespace().next().unwrap()),
            fen,
            |b, fen| {
                b.iter(|| perft(&mut Fen::parse(fen).unwrap().into(), depth, true));
            },
        );
    }
    group.finish();
}

criterion_group!(benches, perft_bench);
criterion_main!(benches);
