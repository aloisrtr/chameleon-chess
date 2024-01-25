use chameleon::position::Position;
use clap::Parser;

#[derive(Parser)]
#[command(author, version)]
struct Arguments {
    depth: u8,
    #[arg(short, long)]
    split_depth: Option<u8>,
    #[arg(short, long)]
    bulk_counting: bool,
    #[arg(short, long)]
    verbose: bool,
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

    for depth in 0..=args.depth {
        println!(
            "depth {depth}: {} nodes",
            perft(
                &mut position,
                depth,
                args.bulk_counting,
                args.split_depth.unwrap_or(0)
            )
        );
    }
}

/// Traverses all nodes accessible from a given position, returning the number of
/// nodes traversed.
fn perft(position: &mut Position, depth_left: u8, bulk_counting: bool, split_at: u8) -> u64 {
    if depth_left == 0 {
        1
    } else if depth_left == 1 && bulk_counting {
        position.moves().len() as u64
    } else {
        if split_at != 0 {
            println!()
        }
        let mut nodes = 0;
        for mv in position.moves() {
            unsafe { position.make_unchecked(mv) };
            let mv_nodes = perft(
                position,
                depth_left - 1,
                bulk_counting,
                split_at.saturating_sub(1),
            );
            nodes += mv_nodes;
            position.unmake();

            if split_at != 0 {
                println!("{mv}: {mv_nodes} nodes")
            }
        }
        nodes
    }
}
