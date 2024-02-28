use benchmark::proof_system::bench_plonkish_backend;

use plonkish_backend::{
    backend::{self, PlonkishBackend, PlonkishCircuit, WitnessEncoding},
    frontend::halo2::{circuit::VanillaPlonk, CircuitExt, Halo2Circuit},
    halo2_curves::bn256::{Bn256, Fr},
    pcs::{multilinear, univariate, CommitmentChunk},
    util::{
        end_timer, start_timer,
        test::std_rng,
        transcript::{InMemoryTranscript, Keccak256Transcript, TranscriptRead, TranscriptWrite},
    },
};

// create test cases

pub mod tests {
    use benchmark::proof_system::bench_plonkish_backend;
    use plonkish_backend::{
        backend::{self, PlonkishBackend, PlonkishCircuit, WitnessEncoding},
        frontend::halo2::{circuit::VanillaPlonk, CircuitExt, Halo2Circuit},
        halo2_curves::bn256::{Bn256, Fr},
        pcs::{multilinear, univariate, CommitmentChunk},
        util::{
            end_timer, start_timer,
            test::std_rng,
            transcript::{InMemoryTranscript, Keccak256Transcript, TranscriptRead, TranscriptWrite},
        },
    };
    use benchmark::proof_system::System;

    #[test]
    fn test_hyperplonk() {
        type GeminiKzg = multilinear::Gemini<univariate::UnivariateKzg<Bn256>>;
        type HyperPlonk = backend::hyperplonk::HyperPlonk<GeminiKzg>;
        // bench_plonkish_backend::<HyperPlonk, Fr>(System::HyperPlonk, 10, c)

        // ChiquitoCircuit::new(
        //     10,
        //     circuit,
        //     assignment_generator: AssignmentGenerator<F, TraceArgs>,
        //     trace_witness: TraceWitness<F>,
        // )
    }
}