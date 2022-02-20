use crate::{
    bcs::{
        constraints::transcript::SimulationTranscriptVar,
        tests::mock::{BCSTestVirtualOracle, MockTest1Verifier},
    },
    iop::{
        bookkeeper::NameSpace,
        constraints::{
            message::MessagesCollectionVar, oracles::VirtualOracleVar, IOPVerifierWithGadget,
        },
        message::ProverRoundMessageInfo,
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
    poly::{domain::Radix2DomainVar, polynomial::univariate::dense::DensePolynomialVar},
    ToBitsGadget, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::{
    constraints::{AbsorbGadget, SpongeWithGadget},
    Absorb,
};
use ark_std::{test_rng, vec, vec::Vec};
use crate::iop::constraints::Nothing;
use crate::iop::message::OracleIndex;
use crate::prelude::MsgRoundRef;

impl<F: PrimeField> VirtualOracleVar<F> for BCSTestVirtualOracle<F> {
    fn constituent_oracle_handles(&self) -> Vec<(MsgRoundRef, Vec<OracleIndex>)> {
        vec![(self.round, vec![(0, true).into()])] // take first oracle with
        // degree bound
    }

    fn evaluate_var(
        &self,
        coset_domain: Radix2DomainVar<F>,
        constituent_oracles: &[Vec<FpVar<F>>],
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let msg2_points = &constituent_oracles[0];
        let poly_var = DensePolynomialVar::from_coefficients_vec(vec![
            FpVar::Constant(F::from(1u64)),
            FpVar::Constant(F::from(2u64)),
            FpVar::Constant(F::from(1u64)),
        ]);
        let eval = coset_domain
            .elements()
            .into_iter()
            .map(|x| poly_var.evaluate(&x))
            .collect::<Result<Vec<_>, SynthesisError>>()?;
        assert_eq!(eval.len(), msg2_points.len());
        Ok(msg2_points.iter().zip(eval).map(|(x, y)| x * y).collect())
    }
}

impl<S: SpongeWithGadget<CF>, CF: PrimeField + Absorb> IOPVerifierWithGadget<S, CF>
    for MockTest1Verifier<CF>
{
    type VerifierParameterVar = Nothing;
    type VerifierOutputVar = Boolean<CF>;
    type PublicInputVar = ();

    fn register_iop_structure_var<MT: Config, MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>>(
        namespace: NameSpace,
        transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
        _verifier_parameter: &Self::VerifierParameterVar,
    ) -> Result<(), SynthesisError>
    where
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<CF>,
    {
        // prover send
        let expected_info =
            ProverRoundMessageInfo::new_using_custom_length_and_localization(256, 2)
                .with_num_message_oracles(2)
                .with_num_short_messages(1)
                .build();
        transcript.receive_prover_current_round(namespace, expected_info, iop_trace!())?;

        // verifier send
        transcript.squeeze_verifier_field_elements(3)?;
        transcript.squeeze_verifier_field_bytes(16)?;
        transcript.submit_verifier_current_round(namespace, iop_trace!());

        // verifier send2
        transcript.squeeze_verifier_field_bits(19)?;
        transcript.submit_verifier_current_round(namespace, iop_trace!());

        // prover send
        let expected_info =
            ProverRoundMessageInfo::new_using_custom_length_and_localization(256, 0)
                .with_num_message_oracles(1)
                .with_num_short_messages(1)
                .build();
        transcript.receive_prover_current_round(namespace, expected_info, iop_trace!())?;

        // prover send2
        let expected_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
            .with_reed_solomon_codes_degree_bounds(vec![8])
            .with_num_short_messages(1)
            .build();
        let prover_oracle_2 =
            transcript.receive_prover_current_round(namespace, expected_info, iop_trace!())?;

        // prover send virtual oracle

        let vo = BCSTestVirtualOracle::new(prover_oracle_2);

        transcript.register_prover_virtual_round(
            namespace,
            vo,
            vec![10],
            vec![10],
            iop_trace!("mock vo"),
        );

        Ok(())
    }

    fn query_and_decide_var(
        cs: ConstraintSystemRef<CF>,
        namespace: NameSpace,
        _verifier_parameter: &Self::VerifierParameterVar,
        _public_input_var: &Self::PublicInputVar,
        _sponge: &mut S::Var,
        transcript_messages: &mut MessagesCollectionVar<CF>,
    ) -> Result<Self::VerifierOutputVar, SynthesisError> {
        // verify if message is indeed correct
        let mut rng = test_rng();
        let cs = ark_relations::ns!(cs, "mock iop query_and_decide");
        let mut random_fe = || FpVar::new_witness(cs.cs(), || Ok(CF::rand(&mut rng))).unwrap();

        let pm1_1: Vec<_> = (0..4).map(|_| random_fe()).collect();
        let pm1_2: Vec<_> = (0..256).map(|_| random_fe()).collect();
        let pm1_3: Vec<_> = (0..256).map(|_| random_fe()).collect();

        transcript_messages
            .prover_round((namespace, 0))
            .short_message(0, iop_trace!())
            .enforce_equal(pm1_1.as_slice())?;

        transcript_messages
            .prover_round((namespace, 0))
            .query_point(
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
        let vm1_1 = transcript_messages.verifier_round((namespace, 0))[0]
            .clone()
            .try_into_field_elements()
            .unwrap();
        assert_eq!(vm1_1.len(), 3);
        let vm1_2 = transcript_messages.verifier_round((namespace, 0))[1]
            .clone()
            .try_into_bytes()
            .unwrap();
        assert_eq!(vm1_2.len(), 16);
        let vm2_1 = transcript_messages.verifier_round((namespace, 1))[0]
            .clone()
            .try_into_bits()
            .unwrap();
        assert_eq!(vm2_1.len(), 19);

        let pm2_1: Vec<_> = vm1_1.into_iter().map(|x| x.square().unwrap()).collect();
        pm2_1.enforce_equal(
            transcript_messages
                .prover_round((namespace, 1))
                .short_message(0, iop_trace!())
                .as_slice(),
        )?;

        let pm2_2: Vec<_> = (0..256u128)
            .map(|x| {
                FpVar::new_witness(cs.cs(), || Ok(CF::from(x))).unwrap()
                    + vm1_2.to_constraint_field().unwrap()[0].clone()
            })
            .collect();

        transcript_messages
            .prover_round((namespace, 1))
            .query_point(
                &[
                    UInt8::constant(19).to_bits_le()?,
                    UInt8::constant(29).to_bits_le()?,
                    UInt8::constant(39).to_bits_le()?,
                ],
                iop_trace!(),
            )?
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
            transcript_messages
                .prover_round((namespace, 2))
                .short_message(0, iop_trace!())
                .as_slice(),
        )?;

        transcript_messages
            .prover_round((namespace, 2))
            .query_point(
                &[vec![Boolean::TRUE], vec![Boolean::FALSE, Boolean::TRUE]],
                iop_trace!(),
            )?; // query 1, 2
        Ok(Boolean::TRUE)
    }
}
