use crate::{
    bcs::{
        bookkeeper::NameSpace,
        tests::FieldMTConfig,
        transcript::{
            test_utils::check_commit_phase_correctness, SimulationTranscript, Transcript,
        },
        MTHashParameters,
    },
    iop::{
        message::{MessagesCollection, ProverRoundMessageInfo, VerifierMessage},
        oracles::{RecordingRoundOracle, RoundOracle, SuccinctRoundOracle},
        prover::IOPProver,
        verifier::IOPVerifier,
    },
    ldt::rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters},
    test_utils::poseidon_parameters,
    Error,
};
use ark_bls12_381::fr::Fr;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::{PrimeField, ToConstraintField};
use ark_ldt::{domain::Radix2CosetDomain, fri::FRIParameters};
use ark_poly::{univariate::DensePolynomial, UVPolynomial};
use ark_sponge::{poseidon::PoseidonSponge, Absorb, CryptographicSponge, FieldElementSize};
use ark_std::{marker::PhantomData, test_rng, vec, vec::Vec, One};
use tracing::Level;

pub(crate) struct MockTestProver<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

/// multiply the first oracle of the message 2 by x^2 + 2x + 1
fn mock_virtual_oracle_for_query<F: PrimeField, O: RoundOracle<F>>(
    namespace: NameSpace,
    iop_messages: &mut MessagesCollection<F, O>,
    queries: &[usize],
    cosets: &[Radix2CosetDomain<F>],
) -> Vec<Vec<Vec<F>>> {
    let span = tracing::span!(Level::INFO, "virtual oracle");
    let _enter = span.enter();
    // calculate f(x) * (x^2 + 2x + 1)

    let msg2_points =
        iop_messages.query_prover_coset((namespace, 2), queries, iop_trace!("mock virtual oracle"));
    assert_eq!(cosets.len(), msg2_points.len());
    msg2_points
        .into_iter()
        .zip(cosets.iter())
        .map(|(msg2_points, coset)| {
            let poly =
                DensePolynomial::from_coefficients_vec(vec![F::one(), F::from(2u64), F::one()]);
            let eval = coset.evaluate(&poly);
            let result = msg2_points[0] // take first oracle
                .clone()
                .into_iter()
                .zip(eval.into_iter())
                .map(|(point, eval)| point * eval)
                .collect::<Vec<_>>();
            vec![result]
        })
        .collect()
}

/// multiply the first oracle of the message 2 by x^2 + 2x + 1
fn mock_virtual_oracle_for_prove<F: PrimeField>(
    evaluation_domain: Radix2CosetDomain<F>,
    constituents: Vec<F>,
) -> Vec<Vec<F>> {
    assert_eq!(constituents.len(), evaluation_domain.size());
    let poly = DensePolynomial::from_coefficients_vec(vec![F::one(), F::from(2u64), F::one()]);
    let poly_eval = evaluation_domain.evaluate(&poly);
    let result = constituents
        .into_iter()
        .zip(poly_eval.into_iter())
        .map(|(constituent, eval)| constituent * eval) // TODO: change it back later
        .collect::<Vec<_>>();
    vec![result]
}

impl<F: PrimeField + Absorb> IOPProver<F> for MockTestProver<F> {
    type ProverParameter = ();
    type RoundOracleRefs = ();
    type PublicInput = ();
    type PrivateInput = ();

    fn prove<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        namespace: NameSpace,
        _oracle_refs: &Self::RoundOracleRefs,
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
        let msg1 = (0..4).map(|_| F::rand(&mut rng));
        transcript.send_message(msg1);
        let msg2 = (0..256).map(|_| F::rand(&mut rng));
        transcript
            .send_message_oracle_with_localization(msg2, 2)
            .unwrap();
        let msg3 = (0..256).map(|_| F::rand(&mut rng));
        transcript
            .send_message_oracle_with_localization(msg3, 2)
            .unwrap();
        transcript
            .submit_prover_current_round(namespace, iop_trace!("mock send"))
            .unwrap();

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

        // prover send
        let msg1 = vm1.into_iter().map(|x| x.square());
        transcript.send_message(msg1);
        let msg2 = (0..256u128).map(|x| {
            let rhs: F = vm2.to_field_elements().unwrap()[0];
            F::from(x) + rhs
        });
        transcript.send_message_oracle(msg2).unwrap();
        transcript
            .submit_prover_current_round(namespace, iop_trace!("mock send2"))
            .unwrap();

        // prover send 2
        let msg1 = (0..6).map(|_| F::rand(&mut rng));
        let msg2 = DensePolynomial::from_coefficients_vec(vec![
            F::from(0x12345u128),
            F::from(0x23456u128),
            F::from(0x34567u128),
            F::from(0x45678u128),
            F::from(0x56789u128),
        ]);
        transcript.send_message(msg1);
        transcript.send_univariate_polynomial(8, &msg2)?;
        transcript
            .submit_prover_current_round(namespace, iop_trace!("mock send3"))
            .unwrap();

        // prover send virtual oracle
        // always make sure arguments have type!
        let virtual_oracle_querier = Box::new(
            move |iop_messages: &mut MessagesCollection<F, RecordingRoundOracle<F>>,
                  queries: &[usize],
                  cosets: &[Radix2CosetDomain<F>]| {
                mock_virtual_oracle_for_query(namespace, iop_messages, queries, cosets)
            },
        );

        let virtual_oracle_evaluations = mock_virtual_oracle_for_prove(
            transcript.ldt_codeword_domain(),
            transcript
                .get_previously_sent_prover_rs_code((namespace, 2), 0)
                .to_vec(),
        );

        transcript.register_prover_virtual_round(
            namespace,
            virtual_oracle_querier,
            virtual_oracle_evaluations,
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
    type OracleRefs = ();
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
        // prover send
        let expected_info = ProverRoundMessageInfo {
            reed_solomon_code_degree_bound: vec![],
            num_message_oracles: 2,
            num_short_messages: 1,
            oracle_length: 256,
            localization_parameter: 2,
        };
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
        let expected_info = ProverRoundMessageInfo {
            reed_solomon_code_degree_bound: vec![],
            num_message_oracles: 1,
            num_short_messages: 1,
            oracle_length: 256,
            localization_parameter: 0,
        };
        transcript.receive_prover_current_round(namespace, expected_info, iop_trace!());

        // prover send2
        let expected_info = ProverRoundMessageInfo {
            reed_solomon_code_degree_bound: vec![8],
            num_message_oracles: 0,
            num_short_messages: 1,
            oracle_length: 128,
            localization_parameter: 0, // managed by LDT
        };
        transcript.receive_prover_current_round(namespace, expected_info, iop_trace!());

        // prover send virtual oracle
        // always make sure arguments have type!
        let coset_eval = Box::new(
            move |iop_messages: &mut MessagesCollection<F, SuccinctRoundOracle<F>>,
                  queries: &[usize],
                  cosets: &[Radix2CosetDomain<F>]| {
                mock_virtual_oracle_for_query(namespace, iop_messages, queries, cosets)
            },
        );

        transcript.register_prover_virtual_round(
            namespace,
            coset_eval,
            vec![10],
            vec![10],
            iop_trace!("mock vo"),
        );
    }

    fn query_and_decide<O: RoundOracle<F>>(
        namespace: NameSpace,
        _verifier_parameter: &Self::VerifierParameter,
        _public_input: &Self::PublicInput,
        _verifier_state: &Self::OracleRefs,
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
            transcript_messages.get_prover_short_message(
                transcript_messages.prover_round_refs_in_namespace(namespace)[0],
                0,
                iop_trace!()
            ),
            &pm1_1
        );
        assert_eq!(
            transcript_messages.query_prover_point(
                transcript_messages.prover_round_refs_in_namespace(namespace)[0],
                &[123, 223],
                iop_trace!("mock query 0")
            ),
            vec![vec![pm1_2[123], pm1_3[123]], vec![pm1_2[223], pm1_3[223]]]
        );

        let vm1_1 = if let VerifierMessage::FieldElements(fe) =
            transcript_messages.get_verifier_message((namespace, 0))[0].clone()
        {
            assert_eq!(fe.len(), 3);
            fe
        } else {
            panic!("invalid vm message type")
        };
        let vm1_2 = if let VerifierMessage::Bytes(bytes) =
            transcript_messages.get_verifier_message((namespace, 0))[1].clone()
        {
            assert_eq!(bytes.len(), 16);
            bytes
        } else {
            panic!("invalid vm message type");
        };

        if let VerifierMessage::Bits(bits) =
            &transcript_messages.get_verifier_message((namespace, 1))[0]
        {
            assert_eq!(bits.len(), 19);
        } else {
            panic!("invalid vm message type");
        }

        let pm2_1: Vec<_> = vm1_1.into_iter().map(|x| x.square()).collect();

        assert_eq!(
            transcript_messages.get_prover_short_message(
                transcript_messages.prover_round_ref(namespace, 1),
                0,
                iop_trace!()
            ),
            &pm2_1
        );

        let pm2_2: Vec<_> = (0..256u128)
            .map(|x| {
                let rhs: F = vm1_2.to_field_elements().unwrap()[0];
                F::from(x) + rhs
            })
            .collect();

        assert_eq!(
            transcript_messages.query_prover_point((namespace, 1), &[19, 29, 39], iop_trace!()),
            vec![vec![pm2_2[19]], vec![pm2_2[29]], vec![pm2_2[39]]]
        );

        let pm3_1: Vec<_> = (0..6).map(|_| F::rand(&mut rng)).collect();
        assert_eq!(
            transcript_messages.get_prover_short_message((namespace, 2), 0, iop_trace!()),
            &pm3_1
        );
        // just query some points
        transcript_messages.query_prover_point((namespace, 2), &vec![1, 2], iop_trace!());

        Ok(true)
    }
}

#[test]
fn check_mock1_commit_phase() {
    let fri_parameters = FRIParameters::new(
        64,
        vec![1, 2, 1],
        Radix2CosetDomain::new_radix2_coset(128, Fr::one()),
    );
    let ldt_pamameters = LinearCombinationLDTParameters {
        fri_parameters,
        num_queries: 1,
    };
    let sponge = PoseidonSponge::new(&poseidon_parameters());
    check_commit_phase_correctness::<
        Fr,
        _,
        FieldMTConfig,
        MockTestProver<Fr>,
        MockTest1Verifier<Fr>,
        LinearCombinationLDT<Fr>,
    >(
        sponge,
        &(),
        &(),
        &(),
        &ldt_pamameters,
        MTHashParameters {
            leaf_hash_param: poseidon_parameters(),
            inner_hash_param: poseidon_parameters(),
        },
    );
}
