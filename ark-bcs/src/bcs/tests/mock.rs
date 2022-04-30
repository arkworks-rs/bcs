use crate::{
    bcs::{simulation_transcript::SimulationTranscript, transcript::Transcript},
    iop::{
        bookkeeper::NameSpace,
        message::{MessagesCollection, OracleIndex, ProverRoundMessageInfo, VerifierMessage},
        oracles::{RoundOracle, VirtualOracle},
        prover::IOPProver,
        verifier::IOPVerifier,
    },
    prelude::MsgRoundRef,
    Error,
};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::{PrimeField, ToConstraintField};
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::{univariate::DensePolynomial, UVPolynomial};
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};
use ark_std::{marker::PhantomData, test_rng, vec, vec::Vec};
use tracing::Level;
use crate::iop::oracles::OracleQuery;

pub(crate) struct MockTestProver<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

pub(crate) struct BCSTestVirtualOracle<F: PrimeField> {
    pub(crate) round: MsgRoundRef,
    _field: PhantomData<F>,
}

impl<F: PrimeField> BCSTestVirtualOracle<F> {
    #[allow(unused)]
    pub(crate) fn new(round: MsgRoundRef) -> Self {
        BCSTestVirtualOracle {
            round,
            _field: PhantomData,
        }
    }
}

impl<F: PrimeField> VirtualOracle<F> for BCSTestVirtualOracle<F> {
    fn constituent_oracle_handles(&self) -> Vec<(MsgRoundRef, Vec<OracleIndex>)> {
        vec![(self.round, vec![(0, true).into()])] // take first oracle with
                                                   // degree bound
    }

    fn evaluate(
        &self,
        codeword_domain: Radix2CosetDomain<F>,
        query: OracleQuery,
        constituent_oracles: &[Vec<F>],
    ) -> Vec<F> {
        // calculate f(x) * (x^2 + 2x + 1)
        let query_domain = query.domain(codeword_domain);
        let msg2_points = &constituent_oracles[0];
        let poly = DensePolynomial::from_coefficients_vec(vec![F::one(), F::from(2u64), F::one()]);
        let eval = query_domain.evaluate(&poly);
        assert_eq!(msg2_points.len(), eval.len());
        msg2_points.iter().zip(eval).map(|(&x, y)| x * y).collect()
    }
}

impl<F: PrimeField + Absorb> IOPProver<F> for MockTestProver<F> {
    type ProverParameter = ();
    type PublicInput = ();
    type PrivateInput = ();

    fn prove<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        namespace: NameSpace,
        _public_input: &Self::PublicInput,
        _private_input: &Self::PrivateInput,
        transcript: &mut Transcript<MT, S, F>,
        _prover_parameter: &Self::ProverParameter,
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb,
    {
        let span = tracing::span!(Level::INFO, "main prove");
        let _enter = span.enter();

        let mut rng = test_rng();

        // prover send
        let msg1 = (0..4).map(|_| F::rand(&mut rng)).collect::<Vec<_>>();
        // transcript.send_message(msg1);
        let msg2 = (0..256).map(|_| F::rand(&mut rng)).collect::<Vec<_>>();
        // transcript
        //     .send_message_oracle_with_localization(msg2, 2)
        //     .unwrap();
        let msg3 = (0..256).map(|_| F::rand(&mut rng)).collect::<Vec<_>>();
        transcript
            .add_prover_round_with_custom_length_and_localization(256, 2)
            .send_short_message(msg1)
            .send_oracle_message_without_degree_bound(msg2)
            .send_oracle_message_without_degree_bound(msg3)
            .submit(namespace, iop_trace!("mock send"))?;

        // verifier send
        let vm1 = transcript.squeeze_verifier_field_elements(&[
            FieldElementSize::Full,
            FieldElementSize::Full,
            FieldElementSize::Full,
        ]);
        let vm2 = transcript.squeeze_verifier_bytes(16);
        transcript.submit_verifier_current_round(namespace, iop_trace!("mock send"));

        // verifier send2
        transcript.squeeze_verifier_bits(19);
        transcript.submit_verifier_current_round(namespace, iop_trace!("mock send2"));

        let msg1 = vm1.into_iter().map(|x| x.square());
        let msg2 = (0..256u128).map(|x| {
            let rhs: F = vm2.to_field_elements().unwrap()[0];
            F::from(x) + rhs
        });
        transcript
            .add_prover_round_with_custom_length_and_localization(256, 0)
            .send_short_message(msg1)
            .send_oracle_message_without_degree_bound(msg2)
            .submit(namespace, iop_trace!("mock send2"))?;

        // prover send 2
        let msg1 = (0..6).map(|_| F::rand(&mut rng)).collect::<Vec<_>>();
        let msg2 = DensePolynomial::from_coefficients_vec(vec![
            F::from(0x12345u128),
            F::from(0x23456u128),
            F::from(0x34567u128),
            F::from(0x45678u128),
            F::from(0x56789u128),
        ]);

        let prover_oracle_2 = transcript
            .add_prover_round_with_codeword_domain()
            .send_short_message(msg1)
            .send_univariate_polynomial(&msg2, 8)
            .submit(namespace, iop_trace!("mock send3"))?;

        // prover send virtual oracle
        // always make sure arguments have type!
        let virtual_oracle = BCSTestVirtualOracle {
            round: prover_oracle_2,
            _field: PhantomData,
        };

        // warning: make sure you register this virtual round again in your verifier
        // (and its constraints) otherwise verification will fail
        transcript.register_prover_virtual_round(
            namespace,
            virtual_oracle,
            vec![10],
            vec![10],
            iop_trace!("mock vo"),
        );

        Ok(())
    }
}

pub(crate) struct MockTest1Verifier<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

impl<S: CryptographicSponge, F: PrimeField + Absorb> IOPVerifier<S, F> for MockTest1Verifier<F> {
    type VerifierOutput = bool;
    type VerifierParameter = ();
    type PublicInput = ();

    fn register_iop_structure<MT: MTConfig<Leaf = [F]>>(
        namespace: NameSpace,
        transcript: &mut SimulationTranscript<MT, S, F>,
        _verifier_parameter: &Self::VerifierParameter,
    ) where
        MT::InnerDigest: Absorb,
    {
        let span = tracing::span!(Level::INFO, "main register");
        let _enter = span.enter();

        let expected_info =
            ProverRoundMessageInfo::new_using_custom_length_and_localization(256, 2)
                .with_num_message_oracles(2)
                .with_num_short_messages(1)
                .build();
        transcript.receive_prover_current_round(namespace, expected_info, iop_trace!());

        // verifier send
        transcript.squeeze_verifier_field_elements(&[
            FieldElementSize::Full,
            FieldElementSize::Full,
            FieldElementSize::Full,
        ]);
        transcript.squeeze_verifier_field_bytes(16);
        transcript.submit_verifier_current_round(namespace, iop_trace!());

        // verifier send2
        transcript.squeeze_verifier_field_bits(19);
        transcript.submit_verifier_current_round(namespace, iop_trace!());

        // prover send
        let expected_info =
            ProverRoundMessageInfo::new_using_custom_length_and_localization(256, 0)
                .with_num_message_oracles(1)
                .with_num_short_messages(1)
                .build();

        transcript.receive_prover_current_round(namespace, expected_info, iop_trace!());

        // prover send2
        let expected_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
            .with_reed_solomon_codes_degree_bounds(vec![8])
            .with_num_short_messages(1)
            .build();
        let prover_oracle_2 =
            transcript.receive_prover_current_round(namespace, expected_info, iop_trace!());

        // prover send virtual oracle
        // always make sure arguments have type!

        let vo = BCSTestVirtualOracle {
            round: prover_oracle_2,
            _field: PhantomData,
        };

        transcript.register_prover_virtual_round(
            namespace,
            vo,
            vec![10],
            vec![10],
            iop_trace!("mock vo"),
        );
    }

    fn query_and_decide<O: RoundOracle<F>>(
        namespace: NameSpace,
        _verifier_parameter: &Self::VerifierParameter,
        _public_input: &Self::PublicInput,
        _sponge: &mut S,
        transcript_messages: &mut MessagesCollection<F, O>,
    ) -> Result<Self::VerifierOutput, Error> {
        let span = tracing::span!(Level::INFO, "main query decide");
        let _enter = span.enter();
        // verify if message is indeed correct
        let mut rng = test_rng();
        let pm1_1: Vec<_> = (0..4).map(|_| F::rand(&mut rng)).collect();
        let pm1_2: Vec<_> = (0..256).map(|_| F::rand(&mut rng)).collect();
        let pm1_3: Vec<_> = (0..256).map(|_| F::rand(&mut rng)).collect();

        assert_eq!(
            transcript_messages
                .prover_round((namespace, 0))
                .short_message(0, iop_trace!()),
            &pm1_1
        );
        assert_eq!(
            transcript_messages
                .prover_round((namespace, 0))
                .query_point(&[123, 223], iop_trace!("mock query 0")),
            vec![vec![pm1_2[123], pm1_3[123]], vec![pm1_2[223], pm1_3[223]]]
        );

        let vm1_1 = if let VerifierMessage::FieldElements(fe) =
            transcript_messages.verifier_round((namespace, 0))[0].clone()
        {
            assert_eq!(fe.len(), 3);
            fe
        } else {
            panic!("invalid vm message type")
        };
        let vm1_2 = if let VerifierMessage::Bytes(bytes) =
            transcript_messages.verifier_round((namespace, 0))[1].clone()
        {
            assert_eq!(bytes.len(), 16);
            bytes
        } else {
            panic!("invalid vm message type");
        };

        if let VerifierMessage::Bits(bits) = &transcript_messages.verifier_round((namespace, 1))[0]
        {
            assert_eq!(bits.len(), 19);
        } else {
            panic!("invalid vm message type");
        }

        let pm2_1: Vec<_> = vm1_1.into_iter().map(|x| x.square()).collect();

        assert_eq!(
            transcript_messages
                .prover_round((namespace, 1))
                .short_message(0, iop_trace!()),
            &pm2_1
        );

        let pm2_2: Vec<_> = (0..256u128)
            .map(|x| {
                let rhs: F = vm1_2.to_field_elements().unwrap()[0];
                F::from(x) + rhs
            })
            .collect();

        assert_eq!(
            transcript_messages
                .prover_round((namespace, 1))
                .query_point(&[19, 29, 39], iop_trace!()),
            vec![vec![pm2_2[19]], vec![pm2_2[29]], vec![pm2_2[39]]]
        );

        let pm3_1: Vec<_> = (0..6).map(|_| F::rand(&mut rng)).collect();
        assert_eq!(
            transcript_messages
                .prover_round((namespace, 2))
                .short_message(0, iop_trace!()),
            &pm3_1
        );
        // just query some points
        transcript_messages
            .prover_round((namespace, 2))
            .query_point(&vec![1, 2], iop_trace!());

        Ok(true)
    }
}
