use crate::{
    bcs::{
        constraints::transcript::SimulationTranscriptVar, tests::mock::MockTest1Verifier,
        transcript::NameSpace,
    },
    iop::{
        constraints::{
            message::{SuccinctRoundOracleVarView, VerifierMessageVar},
            IOPVerifierWithGadget,
        },
        message::{MessagesCollection, ProverRoundMessageInfo},
    },
};
use ark_crypto_primitives::merkle_tree::{constraints::ConfigGadget, Config};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::AllocVar,
    bits::uint8::UInt8,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    ToBitsGadget, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::{
    constraints::{AbsorbGadget, SpongeWithGadget},
    Absorb,
};
use ark_std::{test_rng, vec, vec::Vec};

impl<S: SpongeWithGadget<CF>, CF: PrimeField + Absorb> IOPVerifierWithGadget<S, CF>
    for MockTest1Verifier<CF>
{
    type VerifierOutputVar = Boolean<CF>;
    type PublicInputVar = ();

    fn register_iop_structure_var<MT: Config, MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>>(
        namespace: NameSpace,
        transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
        _verifier_parameter: &Self::VerifierParameter,
    ) -> Result<(), SynthesisError>
    where
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<CF>,
    {
        // prover send
        let expected_info = ProverRoundMessageInfo {
            reed_solomon_code_degree_bound: vec![],
            num_message_oracles: 2,
            num_short_messages: 1,
            oracle_length: 256,
            localization_parameter: 2,
        };
        transcript.receive_prover_current_round(namespace, expected_info, iop_trace!())?;

        // verifier send
        transcript.squeeze_verifier_field_elements(3)?;
        transcript.squeeze_verifier_field_bytes(16)?;
        transcript.submit_verifier_current_round(namespace, iop_trace!());

        // verifier send2
        transcript.squeeze_verifier_field_bits(19)?;
        transcript.submit_verifier_current_round(namespace, iop_trace!());

        // prover send
        let expected_info = ProverRoundMessageInfo {
            reed_solomon_code_degree_bound: vec![],
            num_message_oracles: 1,
            num_short_messages: 1,
            oracle_length: 256,
            localization_parameter: 0,
        };
        transcript.receive_prover_current_round(namespace, expected_info, iop_trace!())?;

        // prover send2
        let expected_info = ProverRoundMessageInfo {
            reed_solomon_code_degree_bound: vec![8],
            num_message_oracles: 0,
            num_short_messages: 1,
            oracle_length: 128,
            localization_parameter: 0,
        };
        transcript.receive_prover_current_round(namespace, expected_info, iop_trace!())?;

        Ok(())
    }

    fn query_and_decide_var(
        cs: ConstraintSystemRef<CF>,
        namespace: NameSpace,
        _verifier_parameter: &Self::VerifierParameter,
        _public_input_var: &Self::PublicInputVar,
        _oracle_refs: &Self::OracleRefs,
        _sponge: &mut S::Var,
        messages_in_commit_phase: &mut MessagesCollection<
            &mut SuccinctRoundOracleVarView<CF>,
            VerifierMessageVar<CF>,
        >,
    ) -> Result<Self::VerifierOutputVar, SynthesisError> {
        // verify if message is indeed correct
        let mut rng = test_rng();
        let cs = ark_relations::ns!(cs, "mock iop query_and_decide");
        let mut random_fe = || FpVar::new_witness(cs.cs(), || Ok(CF::rand(&mut rng))).unwrap();

        let pm1_1: Vec<_> = (0..4).map(|_| random_fe()).collect();
        let pm1_2: Vec<_> = (0..256).map(|_| random_fe()).collect();
        let pm1_3: Vec<_> = (0..256).map(|_| random_fe()).collect();

        messages_in_commit_phase
            .prover_message(namespace, 0)
            .get_short_message(0)
            .enforce_equal(pm1_1.as_slice())?;

        messages_in_commit_phase
            .prover_message(namespace, 0)
            .query(
                &[
                    UInt8::new_witness(cs.cs(), || Ok(123))?.to_bits_le()?,
                    UInt8::new_witness(cs.cs(), || Ok(223))?.to_bits_le()?,
                ],
                iop_trace!(),
            )?
            .into_iter()
            .zip(
                vec![
                    vec![pm1_2[123].clone(), pm1_3[123].clone()],
                    vec![pm1_2[223].clone(), pm1_3[223].clone()],
                ]
                .into_iter(),
            )
            .try_for_each(|(left, right)| left.enforce_equal(&right))?;
        assert!(cs.cs().is_satisfied().unwrap());
        let vm1_1 = messages_in_commit_phase.verifier_message(namespace, 0)[0]
            .clone()
            .try_into_field_elements()
            .unwrap();
        assert_eq!(vm1_1.len(), 3);
        let vm1_2 = messages_in_commit_phase.verifier_message(namespace, 0)[1]
            .clone()
            .try_into_bytes()
            .unwrap();
        assert_eq!(vm1_2.len(), 16);
        let vm2_1 = messages_in_commit_phase.verifier_message(namespace, 1)[0]
            .clone()
            .try_into_bits()
            .unwrap();
        assert_eq!(vm2_1.len(), 19);

        let pm2_1: Vec<_> = vm1_1.into_iter().map(|x| x.square().unwrap()).collect();
        pm2_1.enforce_equal(
            messages_in_commit_phase
                .prover_message(namespace, 1)
                .get_short_message(0)
                .as_slice(),
        )?;

        let pm2_2: Vec<_> = (0..256u128)
            .map(|x| {
                FpVar::new_witness(cs.cs(), || Ok(CF::from(x))).unwrap()
                    + vm1_2.to_constraint_field().unwrap()[0].clone()
            })
            .collect();

        messages_in_commit_phase
            .prover_message(namespace, 1)
            .query(
                &[
                    UInt8::constant(19).to_bits_le()?,
                    UInt8::constant(29).to_bits_le()?,
                    UInt8::constant(39).to_bits_le()?,
                ],
                iop_trace!(),
            )
            .unwrap()
            .into_iter()
            .zip(
                vec![
                    vec![pm2_2[19].clone()],
                    vec![pm2_2[29].clone()],
                    vec![pm2_2[39].clone()],
                ]
                .into_iter(),
            )
            .for_each(|(left, right)| left.enforce_equal(&right).unwrap());

        let pm3_1: Vec<_> = (0..6).map(|_| random_fe()).collect();

        pm3_1.enforce_equal(
            messages_in_commit_phase
                .prover_message(namespace, 2)
                .get_short_message(0)
                .as_slice(),
        )?;

        messages_in_commit_phase
            .prover_message(namespace, 2)
            .query(
                &[vec![Boolean::TRUE], vec![Boolean::FALSE, Boolean::TRUE]],
                iop_trace!(),
            )?; // query 1, 2
        Ok(Boolean::TRUE)
    }
}
