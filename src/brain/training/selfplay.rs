//! # Utilities for generating, storing and loading selfplay data

use std::sync::{Arc, Mutex};

use crate::{
    game::{colour::Colour, position::Position},
    search::SearchConfig,
    uci::endpoint::UciWriter,
};

pub struct FeaturesRecord {
    pub fen: String,
    pub white_active_features: Vec<u16>,
    pub black_active_features: Vec<u16>,
    pub value: f32,
}

/// Generates selfplay data.
pub fn self_play(games: usize, search_config: SearchConfig) -> Vec<FeaturesRecord> {
    let mut records = vec![];

    for _ in 0..games {
        let mut game_record = vec![];
        let mut position = Position::initial();

        let value = loop {
            game_record.push((
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

        for (fen, white_active_features, black_active_features) in game_record {
            // records.push(FeaturesRecord { fen, white_active_features, black_active_features, value:  })
        }
    }

    records
}
