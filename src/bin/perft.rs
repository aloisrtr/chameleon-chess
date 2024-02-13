use chameleon_chess::position::Position;
use clap::Parser;
use rayon::prelude::*;

#[derive(Parser)]
#[command(author, version)]
struct Arguments {
    depth: u8,
    #[arg(short, long)]
    split_depth: Option<u8>,
    #[arg(short, long)]
    bulk_counting: bool,
    #[arg(short, long)]
    divide: bool,
    #[arg(short, long)]
    hash: bool,
    #[arg(short, long)]
    parallel: bool,
    #[arg(short, long)]
    iterative: bool,
    position: Option<String>,
}

fn main() {
    let args = Arguments::parse();

    let mut position = if let Some(fen) = args.position {
        Position::from_fen(&fen).unwrap()
    } else {
        Position::initial()
    };
    println!("{position}\n");

    for depth in (if args.iterative { 1 } else { args.depth })..=args.depth {
        let nodes: u64 = if args.parallel {
            position
                .moves()
                .par_iter()
                .map(|&mv| {
                    let mut position = position.clone();
                    unsafe { position.make_unchecked(mv) };
                    let mv_nodes = perft(&mut position, depth - 1, args.bulk_counting);
                    position.unmake();
                    if args.divide {
                        println!("{}. {mv}: {mv_nodes} nodes", depth - 1);
                    }
                    mv_nodes
                })
                .sum()
        } else {
            position
                .moves()
                .iter()
                .map(|&mv| {
                    unsafe { position.make_unchecked(mv) };
                    let mv_nodes = perft(&mut position, depth - 1, args.bulk_counting);
                    position.unmake();
                    if args.divide {
                        println!("{}. {mv}: {mv_nodes} nodes", depth - 1);
                    }
                    mv_nodes
                })
                .sum()
        };
        println!("depth {depth}: {nodes} nodes",);
    }
}

/// Traverses all nodes accessible from a given position, returning the number of
/// nodes traversed.
fn perft(position: &mut Position, depth_left: u8, bulk_counting: bool) -> u64 {
    if depth_left == 0 {
        1
    } else if depth_left == 1 && bulk_counting {
        position.moves().len() as u64
    } else {
        position
            .moves()
            .iter()
            .map(|&mv| {
                unsafe { position.make_unchecked(mv) };
                let mv_nodes = perft(position, depth_left - 1, bulk_counting);
                position.unmake();
                mv_nodes
            })
            .sum()
    }
}
