//! # NNUE model for training with Burn

use burn::{
    module::Module,
    nn::{loss::MseLoss, Linear, LinearConfig},
    prelude::Backend,
    tensor::{backend::AutodiffBackend, Tensor},
    train::{RegressionOutput, TrainOutput, TrainStep, ValidStep},
};

use crate::brain::{
    feature::FEATURES_COUNT,
    nnue::{ACCUMULATOR_OUT, HIDDEN_OUT, OUTPUT_OUT},
};

use super::batcher::FeaturesBatch;

#[derive(Module, Debug)]
pub struct NnueModel<B: Backend> {
    accumulator: Linear<B>,
    hidden: Linear<B>,
    output: Linear<B>,
}
impl<B: Backend> NnueModel<B> {
    /// Initializes the model, following the size of layers defined in [`crate::brain::nnue`].
    pub fn init(device: &B::Device) -> Self {
        Self {
            accumulator: LinearConfig::new(FEATURES_COUNT, ACCUMULATOR_OUT).init(device),
            hidden: LinearConfig::new(ACCUMULATOR_OUT * 2, HIDDEN_OUT).init(device),
            output: LinearConfig::new(HIDDEN_OUT, OUTPUT_OUT).init(device),
        }
    }

    /// Forward pass using batches.
    /// # Shapes
    /// - Features (for both sides) [batch_size, features]
    /// - Perspectives [batch_size, ]
    /// - Output [batch_size, perspectives]
    pub fn forward(
        &self,
        white_features: Tensor<B, 2>,
        black_features: Tensor<B, 2>,
        perspective: Tensor<B, 2>,
    ) -> Tensor<B, 2> {
        let white_accumulator = self.accumulator.forward(white_features);
        let black_accumulator = self.accumulator.forward(black_features);

        let accumulator = (perspective.clone()
            * Tensor::cat(
                vec![white_accumulator.clone(), black_accumulator.clone()],
                1,
            ))
            + (perspective.neg().add_scalar(1.)
                * Tensor::cat(vec![black_accumulator, white_accumulator], 1));

        let x = accumulator.clamp(0., 1.);
        let x = self.hidden.forward(x).clamp(0., 1.);
        self.output.forward(x)
    }

    /// Returns the MSE regression loss given targets.
    pub fn forward_regression(
        &self,
        white_features: Tensor<B, 2>,
        black_features: Tensor<B, 2>,
        perspective: Tensor<B, 2>,
        targets: Tensor<B, 2>,
    ) -> RegressionOutput<B> {
        let output = self.forward(white_features, black_features, perspective);
        let loss = MseLoss::new().forward(
            output.clone(),
            targets.clone(),
            burn::nn::loss::Reduction::Mean,
        );
        RegressionOutput::new(loss, output, targets)
    }
}
impl<B: AutodiffBackend> TrainStep<FeaturesBatch<B>, RegressionOutput<B>> for NnueModel<B> {
    fn step(&self, item: FeaturesBatch<B>) -> burn::train::TrainOutput<RegressionOutput<B>> {
        let item = self.forward_regression(
            item.white_features,
            item.black_features,
            item.perspectives,
            item.targets,
        );

        TrainOutput::new(self, item.loss.backward(), item)
    }
}

impl<B: Backend> ValidStep<FeaturesBatch<B>, RegressionOutput<B>> for NnueModel<B> {
    fn step(&self, item: FeaturesBatch<B>) -> RegressionOutput<B> {
        self.forward_regression(
            item.white_features,
            item.black_features,
            item.perspectives,
            item.targets,
        )
    }
}
