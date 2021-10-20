use crate::{
    bcs::{
        constraints::{
            proof::BCSProofVar, transcript::SimulationTranscriptVar, MTHashParametersVar,
        },
        transcript::NameSpace,
    },
    iop::{
        constraints::IOPVerifierWithGadget, message::MessagesCollection,
        verifier::IOPVerifierWithNoOracleRefs,
    },
    ldt::{constraints::LDTWithGadget, NoLDT},
};
use ark_crypto_primitives::merkle_tree::{constraints::ConfigGadget, Config};
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_r1cs_std::{boolean::Boolean, eq::EqGadget, fields::fp::FpVar, R1CSVar};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::{
    constraints::{AbsorbGadget, SpongeWithGadget},
    Absorb,
};
use ark_std::{marker::PhantomData, vec::Vec};

/// Verifier Gadget for BCS proof variable.
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
    /// Given a BCS transformed (RS-)IOP proof, verify the correctness of this
    /// proof. `sponge` should be the same state as in beginning of
    /// `BCSProver::prove` function.
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
        V: IOPVerifierWithGadget<S, CF> + IOPVerifierWithNoOracleRefs<S, CF>,
        L: LDTWithGadget<CF>,
        S: SpongeWithGadget<CF>,
    {
        // simulate main prove
        let (verifier_messages, bookkeeper, num_rounds_submitted) = {
            let mut transcript = SimulationTranscriptVar::new_transcript(
                proof,
                &mut sponge,
                |degree| L::ldt_info(ldt_params, degree),
                iop_trace!("BCS root"),
            );
            V::register_iop_structure_var(
                NameSpace::root(iop_trace!("BCS Verify")),
                &mut transcript,
                verifier_parameter,
            )?;
            assert!(
                !transcript.is_pending_message_available(),
                "Sanity check failed: pending verifier message not submitted"
            );
            let num_rounds_submitted = transcript.num_prover_rounds_submitted();
            (
                transcript.reconstructed_verifier_messages,
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
                iop_trace!("BCS LDT root"),
            );
            L::register_iop_structure_var::<_, _, S>(
                ldt_params,
                prover_messages_view
                    .iter()
                    .map(|oracle| oracle.num_reed_solomon_codes_oracles())
                    .sum::<usize>(),
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
            ldt_transcript.reconstructed_verifier_messages
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
            NameSpace::root(iop_trace!("BCS Verify")),
            verifier_parameter,
            public_input,
            &(), // protocol used for BCS should not contain any oracle refs
            &mut sponge,
            &mut MessagesCollection::new(
                prover_messages_view.iter_mut().collect(),
                &verifier_messages,
                &bookkeeper,
            ),
        )?;

        // verify all authentication paths

        let all_prover_oracles = prover_messages_view
            .iter()
            .chain(ldt_prover_messages_view.iter());
        // we clone all the paths because we need to replace its leaf position with
        // verifier calculated one
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
                    return Ok(()); // no queries this round: no need to verify
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

    /// Verify without LDT. If verifier tries to get a low-degree oracle, this
    /// function will panic.
    pub fn verify_with_ldt_disabled<V, S>(
        cs: ConstraintSystemRef<CF>,
        sponge: S::Var,
        proof: &BCSProofVar<MT, MTG, CF>,
        public_input: &V::PublicInputVar,
        verifier_parameter: &V::VerifierParameter,
        hash_params: &MTHashParametersVar<CF, MT, MTG>,
    ) -> Result<V::VerifierOutputVar, SynthesisError>
    where
        V: IOPVerifierWithGadget<S, CF> + IOPVerifierWithNoOracleRefs<S, CF>,
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

    /// Verify without LDT.
    ///
    /// ** Warning **: If verifier tries to get an low-degree oracle, no LDT
    /// will be automatically performed.
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
        V: IOPVerifierWithGadget<S, CF> + IOPVerifierWithNoOracleRefs<S, CF>,
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
