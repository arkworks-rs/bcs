use crate::{
    bcs::{
        prover::BCSProof,
        transcript::{NameSpace, SimulationTranscript},
        MTHashParameters,
    },
    iop::{
        message::MessagesCollection,
        verifier::{IOPVerifier, IOPVerifierWithNoOracleRefs},
    },
    ldt::{NoLDT, LDT},
    Error,
};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::{marker::PhantomData, vec::Vec};

/// Verifier for BCS proof.
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
    /// Given a BCS transformed (RS-)IOP proof, verify the correctness of this
    /// proof. `sponge` should be the same state as in beginning of
    /// `BCSProver::prove` function.
    pub fn verify<V, L, S>(
        sponge: S,
        proof: &BCSProof<MT, F>,
        public_input: &V::PublicInput,
        verifier_parameter: &V::VerifierParameter,
        ldt_params: &L::LDTParameters,
        hash_params: MTHashParameters<MT>,
    ) -> Result<V::VerifierOutput, Error>
    where
        V: IOPVerifierWithNoOracleRefs<S, F>,
        L: LDT<F>,
        S: CryptographicSponge,
    {
        // simulate main prove: reconstruct verifier messages to restore verifier state
        let mut transcript = SimulationTranscript::new_transcript(
            proof,
            sponge,
            |degree| L::ldt_info(ldt_params, degree),
            iop_trace!("IOP Root: BCS proof verify"),
        );

        let root_namespace = NameSpace::root(iop_trace!("BCS Verify: commit phase"));

        V::register_iop_structure::<MT>(root_namespace, &mut transcript, verifier_parameter);
        // sanity check: transcript has not pending message
        assert!(
            !transcript.is_pending_message_available(),
            "Sanity check failed: pending verifier message not submitted"
        );

        let codewords = transcript.bookkeeper.dump_all_prover_messages_in_order();

        let ldt_namespace = transcript.new_namespace(root_namespace, iop_trace!("LDT"));

        // simulate LDT prove: reconstruct LDT verifier messages to restore LDT verifier
        // state
        let num_rs_oracles = codewords
            .clone()
            .into_iter()
            .map(|x| {
                transcript.prover_messages_info[x.index]
                    .reed_solomon_code_degree_bound
                    .len()
            })
            .sum::<usize>();

        L::register_iop_structure(ldt_namespace, ldt_params, num_rs_oracles, &mut transcript);

        debug_assert!(
            !transcript.is_pending_message_available(),
            "Sanity check failed, pending verifier message not submitted"
        );

        // end commit phase
        // start query phase

        // prover message view helps record verify query
        let prover_message_view = proof
            .prover_iop_messages_by_round
            .iter()
            .map(|m| m.get_view())
            .collect::<Vec<_>>();

        let mut messages_in_commit_phase = MessagesCollection::new(
            prover_message_view,
            transcript.reconstructed_verifier_messages,
            transcript.bookkeeper,
        );
        let mut sponge = transcript.sponge;

        // verify LDT

        L::query_and_decide(
            ldt_namespace,
            ldt_params,
            &mut sponge,
            &codewords,
            &mut messages_in_commit_phase,
        )?;

        // verify the protocol (we can use a new view)
        let verifier_result = V::query_and_decide(
            root_namespace,
            verifier_parameter,
            public_input,
            &(),
            &mut sponge,
            &mut messages_in_commit_phase,
        )?;

        // verify all authentication paths

        // we clone all the paths because we need to replace its leaf position with
        // verifier calculated one
        let all_paths = proof.prover_oracles_mt_path.clone();
        let all_mt_roots = &proof.prover_messages_mt_root;

        assert_eq!(
            messages_in_commit_phase.prover_messages.len(),
            all_paths.len()
        );
        assert_eq!(
            messages_in_commit_phase.prover_messages.len(),
            all_mt_roots.len()
        );

        messages_in_commit_phase
            .prover_messages
            .iter()
            .zip(all_paths)
            .zip(all_mt_roots)
            .for_each(|((round_oracle, paths), mt_root)| {
                assert_eq!(round_oracle.coset_queries.len(), paths.len());
                assert_eq!(
                    round_oracle.coset_queries.len(),
                    round_oracle.oracle.queried_cosets.len(),
                    "insufficient queries in verifier code"
                );
                let mt_root = if round_oracle.coset_queries.len() > 0 {
                    mt_root
                        .as_ref()
                        .expect("round oracle has query but has no mt_root")
                } else {
                    return;
                };
                round_oracle
                    .coset_queries
                    .iter()
                    .zip(round_oracle.oracle.queried_cosets.iter())
                    .zip(paths.into_iter())
                    .for_each(|((index, coset), mut path)| {
                        debug_assert_eq!(path.leaf_index, *index);
                        path.leaf_index = *index;
                        assert!(
                            path.verify(
                                &hash_params.leaf_hash_param,
                                &hash_params.inner_hash_param,
                                &mt_root,
                                // flatten by concatenating cosets of all oracles
                                coset
                                    .clone()
                                    .into_iter()
                                    .flatten()
                                    .collect::<Vec<_>>()
                                    .as_slice()
                            )
                            .expect("cannot verify"),
                            "merkle tree verification failed"
                        )
                    })
            });

        Ok(verifier_result)
    }

    /// Verify without LDT. If verifier tries to get a low-degree oracle, this
    /// function will panic.
    pub fn verify_with_ldt_disabled<V, S>(
        sponge: S,
        proof: &BCSProof<MT, F>,
        public_input: &V::PublicInput,
        verifier_parameter: &V::VerifierParameter,
        hash_params: MTHashParameters<MT>,
    ) -> Result<V::VerifierOutput, Error>
    where
        V: IOPVerifier<S, F> + IOPVerifierWithNoOracleRefs<S, F>,
        S: CryptographicSponge,
    {
        Self::verify::<V, NoLDT<_>, S>(
            sponge,
            proof,
            public_input,
            verifier_parameter,
            &None,
            hash_params,
        )
    }

    /// Verify without LDT.
    ///
    /// ** Warning **: If verifier tries to get an low-degree oracle, no LDT
    /// will be automatically performed.
    pub fn verify_with_dummy_ldt<V, S>(
        sponge: S,
        proof: &BCSProof<MT, F>,
        public_input: &V::PublicInput,
        verifier_parameter: &V::VerifierParameter,
        hash_params: MTHashParameters<MT>,
        ldt_codeword_domain: Radix2CosetDomain<F>,
        ldt_codeword_localization_parameter: usize,
    ) -> Result<V::VerifierOutput, Error>
    where
        V: IOPVerifier<S, F> + IOPVerifierWithNoOracleRefs<S, F>,
        S: CryptographicSponge,
    {
        Self::verify::<V, NoLDT<_>, S>(
            sponge,
            proof,
            public_input,
            verifier_parameter,
            &Some((ldt_codeword_domain, ldt_codeword_localization_parameter)),
            hash_params,
        )
    }
}
