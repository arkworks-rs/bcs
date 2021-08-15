use crate::bcs::prover::BCSProof;
use crate::bcs::transcript::{SimulationTranscript, ROOT_NAMESPACE};
use crate::bcs::MTHashParameters;
use crate::iop::verifier::IOPVerifier;
use crate::ldt_trait::{NoLDT, LDT};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::marker::PhantomData;

pub struct BCSVerifier<MT, F>
where
    MT: MTConfig<Leaf = [F]>,
    F: PrimeField + Absorb,
    MT::InnerDigest: Absorb,
{
    _merkle_tree_config: PhantomData<MT>,
    _field: PhantomData<F>,
}

impl<MT, F> BCSVerifier<MT, F>
where
    MT: MTConfig<Leaf = [F]>,
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
        // simulate main prove: reconstruct verifier messages to restore verifier state
        let (verifier_messages, bookkeeper, num_rounds_submitted) = {
            let mut transcript = SimulationTranscript::new_transcript(proof, &mut sponge);
            V::restore_from_commit_phase::<MT>(
                &ROOT_NAMESPACE,
                public_input,
                &mut transcript,
                verifier_parameter,
            );
            // sanity check: transcript has not pending message
            assert!(
                !transcript.is_pending_message_available(),
                "Sanity check failed: pending verifier message not submitted"
            );
            // sanity check: transcript's all prover messages are absorbed
            assert_eq!(
                transcript.current_prover_round,
                proof.prover_iop_messages_by_round.len(),
                "Sanity check failed: transcript's all prover messages are not absorbed"
            );
            let num_rounds_submitted = transcript.num_prover_rounds_submitted();
            (
                transcript.reconstructed_verifer_messages,
                transcript.bookkeeper,
                num_rounds_submitted,
            )
        };

        // construct view of oracle
        let mut prover_messages_view: Vec<_> = proof.prover_iop_messages_by_round
            [..num_rounds_submitted]
            .iter()
            .map(|msg| msg.get_view())
            .collect();
        let mut ldt_prover_messages_view: Vec<_> = proof.prover_iop_messages_by_round
            [num_rounds_submitted..]
            .iter()
            .map(|msg| msg.get_view())
            .collect();

        // simulate LDT prove: reconstruct LDT verifier messages to restore LDT verifier state
        let ldt_verifier_messages = {
            let mut ldt_transcript = SimulationTranscript::new_transcript_with_offset(
                &proof,
                num_rounds_submitted,
                &mut sponge,
            );
            L::restore_from_commit_phase(
                ldt_params,
                prover_messages_view.iter_mut().collect(),
                &mut ldt_transcript,
            );

            // sanity check: transcript has not pending message
            debug_assert!(
                !ldt_transcript.is_pending_message_available(),
                "Sanity check failed, pending verifier message not submitted"
            );
            // sanity check: transcript's all prover messages are absorbed
            let expected_num_ldt_rounds =
                proof.prover_iop_messages_by_round.len() - num_rounds_submitted;
            debug_assert_eq!(ldt_transcript.current_prover_round, expected_num_ldt_rounds);
            ldt_transcript.reconstructed_verifer_messages
        };

        // verify LDT bound
        {
            L::query_and_decide(
                ldt_params,
                &mut sponge,
                prover_messages_view.iter_mut().collect(),
                ldt_prover_messages_view.iter_mut().collect(),
                &ldt_verifier_messages,
            )?; // will return error if verification failed
        }

        // verify the protocol (we can use a new view)
        let verifier_result = V::query_and_decide(
            &ROOT_NAMESPACE,
            verifier_parameter,
            &mut V::initial_state_for_query_and_decision_phase(public_input),
            &mut sponge,
            prover_messages_view.iter_mut().collect(),
            &verifier_messages,
            &bookkeeper,
        )?;

        // verify all authentication paths

        let all_prover_oracles = prover_messages_view
            .iter()
            .chain(ldt_prover_messages_view.iter());
        // we clone all the paths because we need to replace its leaf position with verifier calculated one
        let all_paths = proof.prover_oracles_mt_path.clone();
        let all_mt_roots = &proof.prover_messages_mt_root;

        assert_eq!(
            prover_messages_view.len() + ldt_prover_messages_view.len(),
            all_paths.len()
        );
        assert_eq!(
            prover_messages_view.len() + ldt_prover_messages_view.len(),
            all_mt_roots.len()
        );

        all_prover_oracles
            .zip(all_paths)
            .zip(all_mt_roots)
            .for_each(|((round_oracle, paths), mt_root)| {
                assert_eq!(round_oracle.queries.len(), paths.len());
                assert_eq!(
                    round_oracle.queries.len(),
                    round_oracle.oracle.queried_leaves.len(),
                    "insufficient queries in verifier code"
                );
                let mt_root = if round_oracle.queries.len() > 0 {
                    mt_root
                        .as_ref()
                        .expect("round oracle has query but has no mt_root")
                } else {
                    return;
                };
                round_oracle
                    .queries
                    .iter()
                    .zip(round_oracle.oracle.queried_leaves.iter())
                    .zip(paths.into_iter())
                    .for_each(|((index, leaf), mut path)| {
                        debug_assert_eq!(path.leaf_index, *index);
                        path.leaf_index = *index;
                        assert!(
                            path.verify(
                                &hash_params.leaf_hash_param,
                                &hash_params.inner_hash_param,
                                &mt_root,
                                leaf.as_slice()
                            )
                            .expect("cannot verify"),
                            "merkle tree verification failed"
                        )
                    })
            });

        Ok(verifier_result)
    }

    pub fn verify_without_ldt<V, S>(
        sponge: S,
        proof: &BCSProof<MT, F>,
        public_input: &V::PublicInput,
        verifier_parameter: &V::VerifierParameter,
        hash_params: MTHashParameters<MT>,
    ) -> Result<V::VerifierOutput, Error>
    where
        V: IOPVerifier<S, F>,
        S: CryptographicSponge,
    {
        Self::verify::<V, NoLDT<_>, S>(
            sponge,
            proof,
            public_input,
            verifier_parameter,
            &(),
            hash_params,
        )
    }
}
