//! # NNUE model and accumulator

use std::sync::LazyLock;

use crate::chess::colour::Colour;

use super::feature::FEATURES_COUNT;

static NNUE_NET: LazyLock<Nnue> = LazyLock::new(Nnue::blank);

/// Returns an [`NnueAccumulator`] referencing the static shared NNUE net.
pub fn get_accumulator() -> NnueAccumulator<'static> {
    NNUE_NET.get_accumulator()
}

/// Forward pass using the shared NNUE net.
pub fn forward(accumulator: &NnueAccumulator<'static>, perspective: Colour) -> f32 {
    NNUE_NET.forward(accumulator, perspective)
}

pub const ACCUMULATOR_OUT: usize = 128;
pub const HIDDEN_OUT: usize = 64;
pub const OUTPUT_OUT: usize = 1;

/// Accumulator for the first layer of the NNUE.
pub struct NnueAccumulator<'a> {
    accumulator: [[f32; ACCUMULATOR_OUT]; 2],
    layer: &'a LinearLayer<FEATURES_COUNT, ACCUMULATOR_OUT>,
}
impl<'a> NnueAccumulator<'a> {
    fn with_layer(layer: &'a LinearLayer<FEATURES_COUNT, ACCUMULATOR_OUT>) -> Self {
        Self {
            accumulator: [[0.; ACCUMULATOR_OUT]; 2],
            layer,
        }
    }

    pub fn from_perspective(&self, colour: Colour) -> [f32; ACCUMULATOR_OUT * 2] {
        let mut tensor = [0.; ACCUMULATOR_OUT * 2];
        tensor[..ACCUMULATOR_OUT].copy_from_slice(&self.accumulator[colour as usize]);
        tensor[ACCUMULATOR_OUT..].copy_from_slice(&self.accumulator[colour.inverse() as usize]);
        tensor
    }

    /// Refreshes the accumulator with the given feature set.
    pub fn refresh(&mut self, active_features: &[u16], perspective: Colour) {
        self.accumulator[perspective as usize].copy_from_slice(&self.layer.bias);

        for &feature in active_features {
            for i in 0..ACCUMULATOR_OUT {
                self.accumulator[perspective as usize][i] +=
                    self.layer.weights[feature as usize * ACCUMULATOR_OUT + i];
            }
        }
    }

    /// Updates the accumulator by adding/removing features.
    pub fn update(
        &mut self,
        added_features: &[u16],
        removed_features: &[u16],
        perspective: Colour,
    ) {
        for &feature in added_features {
            for i in 0..ACCUMULATOR_OUT {
                self.accumulator[perspective as usize][i] +=
                    self.layer.weights[feature as usize * ACCUMULATOR_OUT + i]
            }
        }
        for &feature in removed_features {
            for i in 0..ACCUMULATOR_OUT {
                self.accumulator[perspective as usize][i] -=
                    self.layer.weights[feature as usize * ACCUMULATOR_OUT + i]
            }
        }
    }
}

/// NNUE model.
pub struct Nnue {
    accumulator: LinearLayer<FEATURES_COUNT, ACCUMULATOR_OUT>,
    hidden: LinearLayer<{ ACCUMULATOR_OUT * 2 }, HIDDEN_OUT>,
    output: LinearLayer<HIDDEN_OUT, OUTPUT_OUT>,
}
impl Nnue {
    /// Initializes a blank network with all weights to 0.
    pub fn blank() -> Self {
        Self {
            accumulator: LinearLayer::blank(),
            hidden: LinearLayer::blank(),
            output: LinearLayer::blank(),
        }
    }

    /// Returns an [`NnueAccumulator`] referencing this network's first layer.
    pub fn get_accumulator(&self) -> NnueAccumulator {
        NnueAccumulator::with_layer(&self.accumulator)
    }

    pub fn forward(&self, accumulator: &NnueAccumulator, perspective: Colour) -> f32 {
        fn clipped_relu(input: &mut [f32]) {
            for value in input {
                *value = value.clamp(0., 1.)
            }
        }

        let mut input = accumulator.from_perspective(perspective);
        clipped_relu(&mut input);
        let mut input = self.hidden.forward(input);
        clipped_relu(&mut input);
        let output = self.output.forward(input);

        output[0]
    }
}

struct LinearLayer<const IN: usize, const OUT: usize> {
    pub bias: Vec<f32>,
    pub weights: Vec<f32>,
}
impl<const IN: usize, const OUT: usize> LinearLayer<IN, OUT> {
    /// Initializes a [`LinearLayer`] with all weights and biases set to 0.
    pub fn blank() -> Self {
        Self {
            bias: vec![0.; OUT],
            weights: vec![0.; OUT * IN],
        }
    }

    pub fn forward(&self, input: [f32; IN]) -> [f32; OUT] {
        let mut output = [0.; OUT];
        output.copy_from_slice(self.bias.as_slice());

        for (j, output) in output.iter_mut().enumerate() {
            for (i, input) in input.iter().enumerate() {
                *output += input * self.weights[i * OUT + j];
            }
        }

        output
    }
}
