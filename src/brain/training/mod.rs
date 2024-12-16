//! # Self-play NNUE training utilities

use burn::{config::Config, optim::AdamConfig, tensor::backend::AutodiffBackend};

mod batcher;
mod model;
mod selfplay;

#[derive(Config)]
pub struct TrainingConfig {
    pub optimized: AdamConfig,
    #[config(default = 10)]
    pub epochs: usize,
    #[config(default = 64)]
    pub batch_size: usize,
    #[config(default = 6)]
    pub workers: usize,
    #[config(default = 42)]
    pub seed: u64,
    #[config(default = 1.0e-4)]
    pub learning_rate: f64,
}

pub fn train<B: AutodiffBackend>(artifact_dir: &str, config: TrainingConfig, device: B::Device) {
    std::fs::remove_dir_all(artifact_dir).ok();
    std::fs::create_dir_all(artifact_dir).ok();
    config
        .save(format!("{artifact_dir}/config.json"))
        .expect("Failed to save training configuration");

    B::seed(config.seed);
}
