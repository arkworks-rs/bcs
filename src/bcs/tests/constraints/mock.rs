use crate::bcs::constraints::message::{SuccinctRoundOracleVarView, VerifierMessageVar};
use crate::bcs::constraints::transcript::SimulationTranscriptVar;
use crate::bcs::message::{LeafStructure, ProverRoundMessageInfo};
use crate::bcs::tests::mock::MockTest1Verifier;
use crate::bcs::transcript::{MessageBookkeeper, NameSpace};
use crate::iop::constraints::IOPVerifierWithGadget;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::bits::uint8::UInt8;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::{ToBitsGadget, ToConstraintFieldGadget};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::{AbsorbGadget, SpongeWithGadget};
use ark_sponge::Absorb;
use ark_std::test_rng;

impl<S: SpongeWithGadget<CF>, CF: PrimeField + Absorb> IOPVerifierWithGadget<S, CF>
    for MockTest1Verifier<CF>
{
    type VerifierOutputVar = Boolean<CF>;
    type VerifierStateVar = ();
    type PublicInputVar = ();

    fn restore_from_commit_phase_var<MT: Config, MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>>(
        namespace: &NameSpace,
        _public_input: &Self::PublicInputVar,
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
            leaf_info: LeafStructure::default(),
        };
        transcript.receive_prover_current_round(namespace, &expected_info)?;

        // verifier send
        transcript.squeeze_verifier_field_elements(3)?;
        transcript.squeeze_verifier_field_bytes(16)?;
        transcript.submit_verifier_current_round(namespace);

        // verifier send2
        transcript.squeeze_verifier_field_bits(19)?;
        transcript.submit_verifier_current_round(namespace);

        // prover send
        let expected_info = ProverRoundMessageInfo {
            reed_solomon_code_degree_bound: vec![],
            num_message_oracles: 1,
            num_short_messages: 1,
            oracle_length: 256,
            leaf_info: LeafStructure::default(),
        };
        transcript.receive_prover_current_round(namespace, &expected_info)?;

        // prover send2
        let expected_info = ProverRoundMessageInfo {
            reed_solomon_code_degree_bound: vec![],
            num_message_oracles: 0,
            num_short_messages: 1,
            oracle_length: 0,
            leaf_info: LeafStructure::default(),
        };
        transcript.receive_prover_current_round(namespace, &expected_info)?;

        Ok(())
    }

    fn initial_state_for_query_and_decision_phase_var(
        public_input: &Self::PublicInputVar,
    ) -> Result<Self::VerifierStateVar, SynthesisError> {
        Ok(())
    }

    fn query_and_decide_var(
        cs: ConstraintSystemRef<CF>,
        _namespace: &NameSpace,
        _verifier_parameter: &Self::VerifierParameter,
        _verifier_state: &mut Self::VerifierStateVar,
        _random_oracle: &mut S::Var,
        mut prover_message_oracle: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        verifier_messages: &[Vec<VerifierMessageVar<CF>>],
        _bookkeeper: &MessageBookkeeper,
    ) -> Result<Self::VerifierOutputVar, SynthesisError> {
        // verify if message is indeed correct
        let mut rng = test_rng();
        let cs = ark_relations::ns!(cs, "mock iop query_and_decide");
        let mut random_fe = || FpVar::new_witness(cs.cs(), || Ok(CF::rand(&mut rng))).unwrap();

        let pm1_1: Vec<_> = (0..4).map(|_| random_fe()).collect();
        let pm1_2: Vec<_> = (0..256).map(|_| random_fe()).collect();
        let pm1_3: Vec<_> = (0..256).map(|_| random_fe()).collect();

        prover_message_oracle[0]
            .get_short_message(0)
            .enforce_equal(pm1_1.as_slice())?;

        prover_message_oracle[0]
            .query(&[
                UInt8::new_witness(cs.cs(), || Ok(123))?.to_bits_le()?,
                UInt8::new_witness(cs.cs(), || Ok(223))?.to_bits_le()?,
            ])?
            .into_iter()
            .zip(
                vec![
                    vec![pm1_2[123].clone(), pm1_3[123].clone()],
                    vec![pm1_2[223].clone(), pm1_3[223].clone()],
                ]
                .into_iter(),
            )
            .try_for_each(|(left, right)| left.enforce_equal(&right))?;

        let vm1_1 = verifier_messages[0][0]
            .clone()
            .try_into_field_elements()
            .unwrap();
        assert_eq!(vm1_1.len(), 3);
        let vm1_2 = verifier_messages[0][1].clone().try_into_bytes().unwrap();
        assert_eq!(vm1_2.len(), 16);
        let vm2_1 = verifier_messages[1][0].clone().try_into_bits().unwrap();
        assert_eq!(vm2_1.len(), 19);

        let pm2_1: Vec<_> = vm1_1.into_iter().map(|x| x.square().unwrap()).collect();
        pm2_1.enforce_equal(prover_message_oracle[1].get_short_message(0).as_slice())?;

        let pm2_2: Vec<_> = (0..256u128)
            .map(|x| {
                FpVar::new_witness(cs.cs(), || Ok(CF::from(x))).unwrap()
                    + vm1_2.to_constraint_field().unwrap()[0].clone()
            })
            .collect();

        prover_message_oracle[1]
            .query(&[
                UInt8::constant(19).to_bits_le()?,
                UInt8::constant(29).to_bits_le()?,
                UInt8::constant(39).to_bits_le()?,
            ])
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

        pm3_1.enforce_equal(prover_message_oracle[2].get_short_message(0).as_slice())?;

        Ok(Boolean::TRUE)
    }
}
