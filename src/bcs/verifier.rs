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
use std::collections::BTreeMap;
use std::iter::FromIterator;
use crate::bcs::message::MessageOracle;

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
        // construct queryable oracles
        let mut prover_messages: Vec<_> = proof.prover_messages.iter()
            .map(|msg|msg.get_dummy_mut()).collect();
        let mut ldt_prover_messages: Vec<_> = proof.ldt_prover_messages.iter()
            .map(|msg|msg.get_dummy_mut()).collect();

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

        // the helper is to resolve some lifetime issue
        let codeword_oracles_ref: Vec<_> = prover_messages
            .iter_mut()
            .map(|msg| {
                msg.reed_solomon_codes.iter_mut().map(|(oracle,degree)|
                    // those degree has been verified in `restore_state_from_commit_phase`
                    (*degree, oracle))
            })
            .flatten()
            .collect();
        let ldt_verifier_messages = {
            let mut ldt_transcript = SimulationTranscript::new_ldt_transcript(&proof, &mut sponge);
            L::reconstruct_ldt_verifier_messages::<MT, L, S, _>(
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

        // verify LDT bound
        {
            let ldt_prover_messages_ref: Vec<_> = ldt_prover_messages.iter_mut().collect();
            L::query_and_decide(
                ldt_params,
                &mut sponge,
                &codeword_oracles_ref,
                &ldt_prover_messages_ref,
                &ldt_verifier_messages
            )?; // will return error if verification failed
        }

        // verify the protocol
        {
            let prover_messages_ref: Vec<_> = prover_messages.iter_mut().collect();
            V::query_and_decide(
                &ROOT_NAMESPACE,
                verifier_parameter,
                &mut V::initial_state_for_query_and_decision_phase(public_input),
                &mut sponge,
                &prover_messages_ref,
                &verifier_messages,
                &bookkeeper
            )?;
        }

        // Authentication path verification
        for round_msg in proof.prover_messages.iter(){
            // get available queries
            let mut queries = Vec::new();
            let mut queried_leaves = BTreeMap::default();
            round_msg.reed_solomon_codes
                .iter()
                .map(|(oracle, _)|oracle)
                .chain(round_msg.message_oracles.iter())
                .for_each(|oracle|{
                    let queries_current_oracle = oracle.available_indices();
                    if queries.is_empty() {
                        queries = queries_current_oracle;
                        queried_leaves = BTreeMap::from_iter(queries_current_oracle.iter().map(|index|(*index, Vec::new())));
                    }else{
                        assert_eq!(queries, queries_current_oracle, "oracles in the same round have different query indices");
                    }
                    let queries_response_current_oracle = (&oracle).query(&queries).expect("");
                    

                    todo!()

            });


            let queried_leaves = Vec::with_capacity(queries.len());


        }





        todo!()
    }
}
