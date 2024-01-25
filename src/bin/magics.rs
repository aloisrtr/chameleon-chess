use chameleon::square::{Delta, Square};
use rand::prelude::*;

///! Small binary to efficiently generate good magics for sliders' moves
///! hash tables.
pub fn main() {
    println!("Magics generator");
    println!("by Aloïs Rautureau <alois.rautureau@ens-rennes.fr>");

    let args = std::env::args().collect::<Vec<_>>();

    let array_output = if let Some(format) = args.get(1) {
        match format.as_str() {
            "array" => true,
            _ => false,
        }
    } else {
        false
    };

    println!("\nComputing diagonal magics...");
    if !array_output {
        println!(
            "    {:18 } {:18 } bits shift entries",
            "magic", "blocker mask"
        );
    }
    let mut total_size_diagonal = 0;
    let mut diagonal_magics = [0; 64];
    let mut diagonal_bits = [0; 64];
    let mut diagonal_blockers = [0; 64];
    for square in Square::squares_iter() {
        let (blockers_mask, magic, bits) = find_magic(square, false);
        let shift = 64 - bits;
        let size = 1 << bits;
        total_size_diagonal += size;

        diagonal_magics[square as usize] = magic;
        diagonal_bits[square as usize] = bits;
        diagonal_blockers[square as usize] = blockers_mask;

        if !array_output {
            println!(
                "{square}. {magic:#018x} {blockers_mask:#018x} {bits:#4 } {shift:#5 } {size:#7 }",
            );
        }
    }
    if array_output {
        println!("magics:\n{diagonal_magics:?}\n");
        println!("blockers:\n{diagonal_blockers:?}\n");
        println!("bits:\n{diagonal_bits:?}\n");
    }
    println!(
        "\ntotal size of diagonal sliders table: {total_size_diagonal} ({}KiB)\n",
        (total_size_diagonal * std::mem::size_of::<u64>()) / 1000
    );

    println!("\nComputing orthogonal magics...");
    if !array_output {
        println!(
            "    {:18 } {:18 } bits shift entries",
            "magic", "blocker mask"
        );
    }
    let mut total_size_orthogonal = 0;
    let mut orthogonal_magics = [0; 64];
    let mut orthogonal_bits = [0; 64];
    let mut orthogonal_blockers = [0; 64];
    for square in Square::squares_iter() {
        let (blockers_mask, magic, bits) = find_magic(square, true);
        let shift = 64 - bits;
        let size = 1 << bits;
        total_size_orthogonal += size;

        orthogonal_magics[square as usize] = magic;
        orthogonal_bits[square as usize] = bits;
        orthogonal_blockers[square as usize] = blockers_mask;

        if !array_output {
            println!(
                "{square}. {magic:#018x} {blockers_mask:#018x} {bits:#4 } {shift:#5 } {size:#7 }",
            );
        }
    }
    if array_output {
        println!("magics:\n{orthogonal_magics:?}\n");
        println!("blockers:\n{orthogonal_blockers:?}\n");
        println!("bits:\n{orthogonal_bits:?}\n");
    }
    println!(
        "\ntotal size of orthogonal sliders table: {total_size_orthogonal} ({}KiB)",
        (total_size_orthogonal * std::mem::size_of::<u64>()) / 1000
    );
    println!(
        "\ncombined size of tables: {} ({}KiB)",
        total_size_orthogonal + total_size_diagonal,
        ((total_size_orthogonal + total_size_diagonal) * std::mem::size_of::<u64>()) / 1000
    )
}

/// Returns a mask containing all blockers for a diagonal/orthogonal slider on a given square.
const fn blockers(square: Square, orthogonal: bool) -> u64 {
    const DIAGONAL_BLOCKERS: [u64; 64] = {
        let mut result = [0; 64];
        let mut sq = 0;
        while sq < 64 {
            let start_rank = sq / 8;
            let start_file = sq % 8;

            let mut rank = start_rank + 1;
            let mut file = start_file + 1;
            while rank < 7 && file < 7 {
                result[sq] |= 1 << (file + rank * 8);
                rank += 1;
                file += 1;
            }
            rank = start_rank + 1;
            file = start_file.saturating_sub(1);
            while rank < 7 && file > 0 {
                result[sq] |= 1 << (file + rank * 8);
                rank += 1;
                file -= 1;
            }
            rank = start_rank.saturating_sub(1);
            file = start_file + 1;
            while rank > 0 && file < 7 {
                result[sq] |= 1 << (file + rank * 8);
                rank -= 1;
                file += 1;
            }
            rank = start_rank.saturating_sub(1);
            file = start_file.saturating_sub(1);
            while rank > 0 && file > 0 {
                result[sq] |= 1 << (file + rank * 8);
                rank -= 1;
                file -= 1;
            }

            sq += 1;
        }

        result
    };
    const ORTHOGONAL_BLOCKERS: [u64; 64] = {
        let mut result = [0; 64];
        let mut sq = 0;
        while sq < 64 {
            let start_rank = sq / 8;
            let start_file = sq % 8;

            let mut rank = start_rank + 1;
            while rank < 7 {
                result[sq] |= 1 << (start_file + rank * 8);
                rank += 1;
            }
            rank = start_rank.saturating_sub(1);
            while rank > 0 {
                result[sq] |= 1 << (start_file + rank * 8);
                rank -= 1;
            }
            let mut file = start_file + 1;
            while file < 7 {
                result[sq] |= 1 << (file + start_rank * 8);
                file += 1;
            }
            file = start_file.saturating_sub(1);
            while file > 0 {
                result[sq] |= 1 << (file + start_rank * 8);
                file -= 1;
            }

            sq += 1;
        }

        result
    };

    if orthogonal {
        ORTHOGONAL_BLOCKERS[square as usize]
    } else {
        DIAGONAL_BLOCKERS[square as usize]
    }
}

/// Generates a set of squares accessible from square with the given blockers.
fn moves(square: Square, blockers: u64, orthogonal: bool) -> u64 {
    let mut result = 0;

    let deltas = if orthogonal {
        [Delta::North, Delta::South, Delta::East, Delta::West]
    } else {
        [
            Delta::NorthEast,
            Delta::SouthEast,
            Delta::NorthWest,
            Delta::SouthWest,
        ]
    };

    for delta in deltas {
        let Some(mut current_square) = square.translate(delta) else {
            continue;
        };
        loop {
            result |= 1 << current_square as u8;
            if (blockers & (1 << current_square as u8)) != 0 {
                break;
            } else if let Some(sq) = current_square.translate(delta) {
                current_square = sq;
            } else {
                break;
            }
        }
    }

    result
}

/// Given a square and a fixed shift, returns a blocker mask, magic, shift and corresponding array
/// of moves for a diagonally/orthogonally moving slider on said square.
fn find_magic(square: Square, orthogonal: bool) -> (u64, u64, u8) {
    const fn table_index(blockers_mask: u64, magic: u64, shift: u8, blockers: u64) -> usize {
        ((blockers & blockers_mask).wrapping_mul(magic) >> shift) as usize
    }

    let blockers_mask = blockers(square, orthogonal);
    let bits = blockers_mask.count_ones() as u8;
    'check: loop {
        // Clear the table if previously used
        let mut table = vec![0; 1 << bits];

        // Create a random magic value (low amount of bits set).
        let magic = random::<u64>() & random::<u64>() & random::<u64>();

        // Generate moves for every blocker configuration.
        let mut blockers = 0;
        'blockers: loop {
            let moves = moves(square, blockers, orthogonal);

            let index = table_index(blockers_mask, magic, 64 - bits, blockers);
            let Some(entry) = table.get_mut(index) else {
                continue 'check;
            };

            // Writing on empty slot
            if *entry == 0 {
                *entry = moves;
            }
            // The slot is filled and colliding, this magic will not work
            else if *entry != moves {
                continue 'check;
            }

            blockers = (blockers - blockers_mask) & blockers_mask;
            if blockers == 0 {
                break 'blockers;
            }
        }
        return (blockers_mask, magic, bits);
    }
}
