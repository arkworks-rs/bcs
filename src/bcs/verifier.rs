use crate::bcs::message::MessageOracle;
use crate::bcs::prover::BCSProof;
use crate::bcs::transcript::{SimulationTranscript, ROOT_NAMESPACE};
use crate::bcs::MTHashParameters;
use crate::iop::verifier::IOPVerifier;
use crate::ldt_trait::LDT;
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::marker::PhantomData;
use std::borrow::Borrow;

pub struct BCSVerifier<MT, F>
where
    MT: MTConfig<Leaf = Vec<F>>,
    F: PrimeField + Absorb,
    MT::InnerDigest: Absorb,
{
    _merkle_tree_config: PhantomData<MT>,
    _field: PhantomData<F>,
}

impl<MT, F> BCSVerifier<MT, F>
where
    MT: MTConfig<Leaf = Vec<F>>,
    F: PrimeField + Absorb,
    MT::InnerDigest: Absorb,
{
    pub fn verify<V, L, S>(
        mut sponge: S,
        proof: &BCSProof<MT, F>,
        public_input: &V::PublicInput,
        verifier_parameter: &V::VerifierParameter,
        ldt_params: &L::LDTParameters,
        hash_params: MTHashParameters<MT>,
    ) -> Result<V::VerifierOutput, Error>
    where
        V: IOPVerifier<S, F>,
        L: LDT<F>,
        S: CryptographicSponge,
    {
        // reconstruct verifier messages to restore verifier state
        let (verifier_messages, bookkeeper) = {
            let mut transcript = SimulationTranscript::new_main_transcript(proof, &mut sponge);
            V::restore_state_from_commit_phase::<MT, L>(
                &ROOT_NAMESPACE,
                public_input,
                &mut transcript,
                verifier_parameter,
            );
            // sanity check: transcript has not pending message
            debug_assert!(
                !transcript.is_pending_message_available(),
                "Sanity check failed, pending verifier message not submitted"
            );
            // sanity check: transcript's all prover messages are absorbed
            debug_assert!(transcript.current_prover_round == proof.prover_messages.len());
            (
                transcript.reconstructed_verifer_messages,
                transcript.bookkeeper,
            )
        };
        // reconstruct LDT verifier messages to restore LDT verifier state
        let ldt_verifier_messages = {
            let codeword_oracles_ref: Vec<_> = proof
                .prover_messages
                .iter()
                .map(|msg| {
                    msg.reed_solomon_codes.iter().map(|(oracle,degree)|
                        // those degree has been verified in `restore_state_from_commit_phase`
                        (*degree, oracle))
                })
                .flatten()
                .collect();
            let mut ldt_transcript = SimulationTranscript::new_ldt_transcript(proof, &mut sponge);
            L::reconstruct_ldt_verifier_messages::<MT, L, S>(
                ldt_params,
                &codeword_oracles_ref,
                &mut ldt_transcript,
            );
            // sanity check: transcript has not pending message
            debug_assert!(
                !ldt_transcript.is_pending_message_available(),
                "Sanity check failed, pending verifier message not submitted"
            );
            // sanity check: transcript's all prover messages are absorbed
            debug_assert!(ldt_transcript.current_prover_round == proof.ldt_prover_messages.len());
            ldt_transcript.reconstructed_verifer_messages
        };

        todo!()
    }
}
