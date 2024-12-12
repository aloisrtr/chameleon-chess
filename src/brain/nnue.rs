//! # NNUE model and accumulator

use crate::board::colour::Colour;

use super::feature::FEATURES_COUNT;
pub const HIDDEN_LAYER_IN: usize = 128;
pub const HIDDEN_LAYER_OUT: usize = 64;
pub const OUTPUT_SIZE: usize = 1;

/// Accumulator for the first layer of the NNUE.
pub struct NnueAccumulator([[f32; HIDDEN_LAYER_IN]; 2]);
impl NnueAccumulator {
    pub fn perspective(&self, colour: Colour) -> [f32; HIDDEN_LAYER_IN * 2] {
        let mut tensor = [0.; HIDDEN_LAYER_IN * 2];
        for i in 0..HIDDEN_LAYER_IN {
            tensor[i] = self.0[colour as usize][i];
            tensor[i + HIDDEN_LAYER_IN] = self.0[colour.inverse() as usize][i];
        }
        tensor
    }
}

/// NNUE model.
pub struct Nnue {
    l1: LinearLayer<FEATURES_COUNT, HIDDEN_LAYER_IN>,
    l2: LinearLayer<{ HIDDEN_LAYER_IN * 2 }, HIDDEN_LAYER_OUT>,
    l3: LinearLayer<HIDDEN_LAYER_OUT, OUTPUT_SIZE>,
}
impl Nnue {
    pub fn forward(&self, accumulator: &NnueAccumulator, perspective: Colour) {
        let mut buffer = [0.; HIDDEN_LAYER_IN * 2];
        let input = accumulator.perspective(perspective);

        let mut current_input = input.as_slice();
        Self::clipped_relu(current_input, &mut buffer[0..current_input.len()]);
        current_input = &buffer[0..current_input.len()];
        self.l1
            .forward(current_input, &mut buffer[0..HIDDEN_LAYER_OUT]);
    }

    pub fn clipped_relu(input: &[f32], output: &mut [f32]) {
        debug_assert_eq!(input.len(), output.len());
        for (src, dest) in input.iter().zip(output.iter_mut()) {
            *dest = src.max(0.).min(1.)
        }
    }
}

struct LinearLayer<const IN: usize, const OUT: usize> {
    pub bias: [f32; IN],
    pub weights: [[f32; IN]; OUT],
}
impl<const IN: usize, const OUT: usize> LinearLayer<IN, OUT> {
    pub fn forward(&self, input: &[f32], output: &mut [f32]) {
        debug_assert_eq!(input.len(), IN);
        debug_assert_eq!(output.len(), OUT);

        // Copy bias
        output.copy_from_slice(&self.bias);

        for i in 0..IN {
            for j in 0..OUT {
                output[j] += input[i] * self.weights[i][j];
            }
        }
    }
}
