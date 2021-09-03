use crate::bcs::constraints::proof::BCSProofVar;
use crate::bcs::constraints::transcript::SimulationTranscriptVar;
use crate::bcs::constraints::MTHashParametersVar;
use crate::bcs::transcript::ROOT_NAMESPACE;
use crate::iop::constraints::IOPVerifierWithGadget;
use crate::ldt::constraints::LDTWithGadget;
use crate::ldt::NoLDT;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::{AbsorbGadget, SpongeWithGadget};
use ark_sponge::Absorb;
use std::marker::PhantomData;

pub struct BCSVerifierGadget<MT, MTG, CF>
where
    MT: Config,
    MTG: ConfigGadget<MT, CF>,
    CF: PrimeField + Absorb,
{
    _merkle_tree_config: PhantomData<(MT, MTG)>,
    _field: PhantomData<CF>,
}

impl<MT, MTG, CF> BCSVerifierGadget<MT, MTG, CF>
where
    MT: Config,
    MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>,
    CF: PrimeField + Absorb,
    MT::InnerDigest: Absorb,
    MTG::InnerDigest: AbsorbGadget<CF>,
{
    pub fn verify<V, L, S>(
        cs: ConstraintSystemRef<CF>,
        mut sponge: S::Var,
        proof: &BCSProofVar<MT, MTG, CF>,
        public_input: &V::PublicInputVar,
        verifier_parameter: &V::VerifierParameter,
        ldt_params: &L::LDTParameters,
        hash_params: &MTHashParametersVar<CF, MT, MTG>,
    ) -> Result<V::VerifierOutputVar, SynthesisError>
    where
        V: IOPVerifierWithGadget<S, CF>,
        L: LDTWithGadget<CF>,
        S: SpongeWithGadget<CF>,
    {
        // simulate main prove
        let (verifier_messages, bookkeeper, num_rounds_submitted) = {
            let mut transcript =
                SimulationTranscriptVar::new_transcript(proof, &mut sponge, |degree| {
                    L::ldt_info(ldt_params, degree)
                });
            V::restore_from_commit_phase_var(
                &ROOT_NAMESPACE,
                public_input,
                &mut transcript,
                verifier_parameter,
            )?;
            assert!(
                !transcript.is_pending_message_available(),
                "Sanity check failed: pending verifier message not submitted"
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

        // simulate LDT prove: reconstruct LDT verifier messages
        let ldt_verifier_messages = {
            let mut ldt_transcript = SimulationTranscriptVar::new_transcript_with_offset(
                proof,
                num_rounds_submitted,
                &mut sponge,
                |_| panic!("LDT transcript cannot send LDT oracle."),
            );
            L::restore_from_commit_phase_var::<_, _, S>(
                ldt_params,
                prover_messages_view.iter_mut().collect(),
                &mut ldt_transcript,
            )?;
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

        // LDT verify
        L::query_and_decide_var::<S>(
            ldt_params,
            &mut sponge,
            prover_messages_view.iter_mut().collect(),
            ldt_prover_messages_view.iter_mut().collect(),
            &ldt_verifier_messages,
        )?;

        // verify the protocol
        let verifier_result_var = V::query_and_decide_var(
            cs.clone(),
            &ROOT_NAMESPACE,
            verifier_parameter,
            &mut V::initial_state_for_query_and_decision_phase_var(public_input)?,
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
        let all_paths = &proof.prover_oracles_mt_path;
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
            .try_for_each(|((round_oracle, paths), mt_root)| {
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
                    return Ok(()); /*no queries this round: no need to verify*/
                };
                round_oracle
                    .coset_queries
                    .iter()
                    .zip(round_oracle.oracle.queried_cosets.iter())
                    .zip(paths.iter())
                    .try_for_each(|((index, coset), path)| {
                        let mut path = path.clone();
                        let old_path = path.get_leaf_position().value().unwrap();
                        path.set_leaf_position(index.clone());
                        let new_path = path.get_leaf_position().value().unwrap();
                        assert_eq!(old_path, new_path);
                        path.verify_membership(
                            &hash_params.leaf_params,
                            &hash_params.inner_params,
                            mt_root,
                            // flatten by concatenating cosets of all queries
                            coset
                                .iter()
                                .flatten()
                                .map(|x| x.clone())
                                .collect::<Vec<_>>()
                                .as_slice(),
                        )?
                        .enforce_equal(&Boolean::TRUE)
                    })?;
                Ok(())
            })?;

        Ok(verifier_result_var)
    }

    pub fn verify_with_ldt_disabled<V, S>(
        cs: ConstraintSystemRef<CF>,
        sponge: S::Var,
        proof: &BCSProofVar<MT, MTG, CF>,
        public_input: &V::PublicInputVar,
        verifier_parameter: &V::VerifierParameter,
        hash_params: &MTHashParametersVar<CF, MT, MTG>,
    ) -> Result<V::VerifierOutputVar, SynthesisError>
    where
        V: IOPVerifierWithGadget<S, CF>,
        S: SpongeWithGadget<CF>,
    {
        Self::verify::<V, NoLDT<CF>, S>(
            cs,
            sponge,
            proof,
            public_input,
            verifier_parameter,
            &None,
            hash_params,
        )
    }

    pub fn verify_with_dummy_ldt<V, S>(
        cs: ConstraintSystemRef<CF>,
        sponge: S::Var,
        proof: &BCSProofVar<MT, MTG, CF>,
        public_input: &V::PublicInputVar,
        verifier_parameter: &V::VerifierParameter,
        hash_params: &MTHashParametersVar<CF, MT, MTG>,
        ldt_codeword_domain: Radix2CosetDomain<CF>,
        ldt_codeword_localization_parameter: usize,
    ) -> Result<V::VerifierOutputVar, SynthesisError>
    where
        V: IOPVerifierWithGadget<S, CF>,
        S: SpongeWithGadget<CF>,
    {
        Self::verify::<V, NoLDT<CF>, S>(
            cs,
            sponge,
            proof,
            public_input,
            verifier_parameter,
            &Some((ldt_codeword_domain, ldt_codeword_localization_parameter)),
            hash_params,
        )
    }
}
