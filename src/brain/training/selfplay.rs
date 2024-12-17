//! # Utilities for generating, storing and loading selfplay data

use std::{
    fs::File,
    path::Path,
    sync::{Arc, Mutex},
};

use bitstream_io::{BigEndian, BitRead, BitReader, BitWrite, BitWriter};

use crate::{
    game::{colour::Colour, fen::Fen, position::Position},
    search::SearchConfig,
    uci::endpoint::UciWriter,
};

pub struct FeaturesRecord {
    pub fen: Fen,
    pub white_active_features: Vec<u16>,
    pub black_active_features: Vec<u16>,
    pub value: f32,
}

/// Saves records of features to a file in a compressed format.
pub fn save_self_play<P: AsRef<Path>>(file: P, records: &[FeaturesRecord]) -> std::io::Result<()> {
    let f = File::options()
        .append(true)
        .read(true)
        .create(true)
        .open(&file)?;
    let mut writer = BitWriter::endian(f, BigEndian);

    let mut white_wins = 0;
    let mut black_wins = 0;
    let mut total = 0;
    for record in records {
        record.fen.compress(&mut writer).unwrap();
        writer.write(32, record.value.to_bits())?;
        total += 1;
        if record.value > 0. && record.fen.side_to_move == Colour::White {
            white_wins += 1
        } else if record.value < 0. && record.fen.side_to_move == Colour::White {
            black_wins += 1
        }
    }
    log::info!(
        "Saved {} position records to {}",
        records.len(),
        file.as_ref().to_str().unwrap()
    );
    log::info!(
        "White wins: {}%, draws: {}%, black wins: {}%",
        white_wins as f32 / total as f32,
        1. / ((white_wins + black_wins) as f32 / total as f32),
        black_wins as f32 / total as f32
    );
    Ok(())
}

/// Loads at most `n` records from the given file.
pub fn load_self_play<P: AsRef<Path>>(file: P, n: usize) -> std::io::Result<Vec<FeaturesRecord>> {
    let f = File::open(&file)?;
    let mut reader = BitReader::endian(f, BigEndian);

    let mut records = vec![];

    while let Ok(fen) = Fen::decompress(&mut reader) {
        let value = f32::from_bits(reader.read(32)?);
        let position = Position::from_fen(&fen);
        records.push(FeaturesRecord {
            fen,
            value,
            white_active_features: position.active_features(Colour::White),
            black_active_features: position.active_features(Colour::Black),
        });

        if records.len() >= n {
            break;
        }
    }

    log::info!(
        "Loaded {} position records from {}",
        records.len(),
        file.as_ref().to_str().unwrap()
    );

    Ok(records)
}

/// Generates selfplay data.
pub fn self_play(games: usize, search_config: SearchConfig) -> Vec<FeaturesRecord> {
    let mut records = vec![];

    log::info!("Generating {games} games from self play");
    log::info!("Search config: {search_config:?}");

    for _ in 0..games {
        let mut game_records = vec![];
        let mut position = Position::initial();

        let value = loop {
            game_records.push((
                position.fen(),
                position.active_features(Colour::White),
                position.active_features(Colour::Black),
            ));
            let mut handle = search_config.clone().go(
                position.clone(),
                Arc::new(Mutex::new(UciWriter::new(std::io::stderr()))),
            );
            handle.wait();
            if let Some(action) = handle.best_action() {
                position.make_legal(action)
            } else {
                break handle.value();
            }
        };

        log::info!("Generated {} records", game_records.len());

        for (fen, white_active_features, black_active_features) in game_records {
            records.push(FeaturesRecord {
                fen,
                white_active_features,
                black_active_features,
                value: value.exploitation_score(fen.side_to_move),
            })
        }
    }

    log::info!("Generated a total of {} records", records.len());
    records
}
