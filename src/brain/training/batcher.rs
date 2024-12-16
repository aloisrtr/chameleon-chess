//! # Batcher implementation for NNUE features

use burn::{data::dataloader::batcher::Batcher, prelude::Backend, tensor::Tensor};

pub struct FeaturesBatch<B: Backend> {
    pub white_features: Tensor<B, 2>,
    pub black_features: Tensor<B, 2>,
    pub perspectives: Tensor<B, 2>,
    pub targets: Tensor<B, 2>,
}

pub struct FeaturesBatcher<B: Backend> {
    device: B::Device,
}
impl<B: Backend> FeaturesBatcher<B> {
    pub fn new(device: B::Device) -> Self {
        Self { device }
    }
}
impl<B: Backend> Batcher<(), FeaturesBatch<B>> for FeaturesBatcher<B> {
    fn batch(&self, items: Vec<()>) -> FeaturesBatch<B> {
        todo!()
    }
}
