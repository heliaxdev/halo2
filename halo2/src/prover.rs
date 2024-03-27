use halo2_gadgets::endoscale::EndoscaleInstructions;
use halo2_proofs::transcript::{EncodedChallenge, TranscriptRead};

use crate::transcript::TranscriptInstructions;

use super::accumulator;
use pasta_curves::vesta;

/// Application circuit
struct AppCircuit {}

/// Recursive verifier
struct Verifier<E, EndoscaleChip, TranscriptChip, TR>
where
    E: EncodedChallenge<vesta::Affine>,
    EndoscaleChip: EndoscaleInstructions<vesta::Affine>,
    TranscriptChip: TranscriptInstructions<vesta::Affine>,
    TR: TranscriptRead<vesta::Affine, E> + Clone,
{
    application: AppCircuit,
    acc_verifier: accumulator::Verifier<E, EndoscaleChip, TranscriptChip, TR>,
}
