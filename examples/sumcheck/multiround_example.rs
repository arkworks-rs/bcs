#![allow(unused)]
use ark_bls12_381::fr::Fr;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_ldt::{domain::Radix2CosetDomain, fri::FRIParameters};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Radix2EvaluationDomain, UVPolynomial,
};
use ark_serialize::CanonicalSerialize;
use ark_sponge::{poseidon::PoseidonSponge, Absorb, CryptographicSponge, FieldElementSize};
use ark_std::{marker::PhantomData, test_rng, One};

use ark_bcs::{
    bcs::{
        prover::BCSProof,
        transcript::{NameSpace, SimulationTranscript, Transcript},
        verifier::BCSVerifier,
        MTHashParameters,
    },
    iop::{
        message::{MessagesCollection, ProverRoundMessageInfo, RoundOracle, VerifierMessage},
        prover::IOPProver,
        verifier::IOPVerifier,
        ProverParam,
    },
    ldt::rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters},
    Error,
};

use crate::{
    simple_sumcheck::{
        SimpleSumcheck, SumcheckOracleRef, SumcheckProverParameter, SumcheckPublicInput,
        SumcheckVerifierParameter,
    },
    test_utils::{poseidon_parameters, FieldMTConfig},
};

/// This protocol takes 2 polynomial coefficients as private input (as well as
/// its sum over summation domain). The protocol send those three oracles to
/// verifier, and run simple sumcheck on each of them.
pub struct SumcheckMultiroundExample<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct Parameter<F: PrimeField + Absorb> {
    evaluation_domain: Radix2EvaluationDomain<F>,
    summation_domain: Radix2EvaluationDomain<F>,
    degrees: (usize, usize), // degree of `poly1` and `poly2`
}

impl<F: PrimeField + Absorb> ProverParam for Parameter<F> {
    type VerifierParameter = Self;

    fn to_verifier_param(&self) -> Self::VerifierParameter {
        self.clone()
    }
}

#[derive(Clone)]
pub struct PublicInput<F: PrimeField + Absorb> {
    sums: (F, F), // sum of `poly0` over summation domain, sum of `poly1` over summation domain
}

pub struct PrivateInput<F: PrimeField + Absorb>(
    DensePolynomial<F>, // `poly0` coefficients
    DensePolynomial<F>, // `poly1` coefficients
);

impl<F: PrimeField + Absorb> IOPProver<F> for SumcheckMultiroundExample<F> {
    type ProverParameter = Parameter<F>;
    type RoundOracleRefs = ();
    type PublicInput = PublicInput<F>;
    type PrivateInput = PrivateInput<F>;

    fn prove<MT: Config<Leaf = [F]>, S: CryptographicSponge>(
        namespace: NameSpace,
        _oracle_refs: &Self::RoundOracleRefs,
        public_input: &Self::PublicInput,
        private_input: &Self::PrivateInput,
        transcript: &mut Transcript<MT, S, F>,
        prover_parameter: &Self::ProverParameter,
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb,
    {
        // receive r0
        let r0 = transcript
            .squeeze_verifier_field_elements(&[FieldElementSize::Full])
            .remove(0);
        transcript.submit_verifier_current_round(namespace, iop_trace!("r0"));

        // multiply poly0 by r0
        let poly0 = DensePolynomial::from_coefficients_vec(
            private_input
                .0
                .coeffs
                .iter()
                .map(|coeff| *coeff * &r0)
                .into_iter()
                .collect::<Vec<_>>(),
        );
        let asserted_sum0 = public_input.sums.0 * r0;

        // send one polynomial as oracle.
        transcript.send_univariate_polynomial(prover_parameter.degrees.0, &poly0)?;
        let poly0_ref = transcript.submit_prover_current_round(namespace, iop_trace!("poly0"))?;
        // invoke sumcheck polynomial on first polynomial
        let ns0 = transcript.new_namespace(namespace, iop_trace!("first sumcheck protocol"));
        SimpleSumcheck::prove(
            ns0,
            &SumcheckOracleRef::new(poly0_ref),
            &SumcheckPublicInput::new(asserted_sum0, 0),
            &(),
            transcript,
            &SumcheckProverParameter {
                coeffs: poly0,
                summation_domain: prover_parameter.summation_domain,
                evaluation_domain: prover_parameter.evaluation_domain,
                degree: prover_parameter.degrees.0,
            },
        )?;

        // receive r1
        let r1 = transcript
            .squeeze_verifier_field_elements(&[FieldElementSize::Full])
            .remove(0);
        transcript.submit_verifier_current_round(namespace, iop_trace!("r1"));

        // multiply poly0 by r0
        let poly1 = DensePolynomial::from_coefficients_vec(
            private_input
                .1
                .coeffs
                .iter()
                .map(|coeff| *coeff * &r1)
                .into_iter()
                .collect::<Vec<_>>(),
        );
        let asserted_sum1 = public_input.sums.1 * r1;

        transcript.send_univariate_polynomial(prover_parameter.degrees.1, &poly1)?;
        let poly1_ref = transcript.submit_prover_current_round(namespace, iop_trace!("poly1"))?;

        // invoke sumcheck polynomial on second polynomial
        let ns1 = transcript.new_namespace(namespace, iop_trace!("second sumcheck protocol"));
        SimpleSumcheck::prove(
            ns1,
            &SumcheckOracleRef::new(poly1_ref),
            &SumcheckPublicInput::new(asserted_sum1, 0),
            &(),
            transcript,
            &SumcheckProverParameter {
                coeffs: poly1,
                summation_domain: prover_parameter.summation_domain,
                evaluation_domain: prover_parameter.evaluation_domain,
                degree: prover_parameter.degrees.1,
            },
        )?;

        Ok(())
    }
}

impl<S: CryptographicSponge, F: PrimeField + Absorb> IOPVerifier<S, F>
    for SumcheckMultiroundExample<F>
{
    type VerifierOutput = bool;
    type VerifierParameter = Parameter<F>;
    type OracleRefs = ();
    type PublicInput = PublicInput<F>;

    fn register_iop_structure<MT: Config<Leaf = [F]>>(
        namespace: NameSpace,
        transcript: &mut SimulationTranscript<MT, S, F>,
        verifier_parameter: &Self::VerifierParameter,
    ) where
        MT::InnerDigest: Absorb,
    {
        // verifier send r0
        transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full]);
        transcript.submit_verifier_current_round(namespace, iop_trace!("r0"));

        // receive poly0
        transcript.receive_prover_current_round(
            namespace,
            ProverRoundMessageInfo::new(
                vec![verifier_parameter.degrees.0],
                0,
                0,
                verifier_parameter.evaluation_domain.size(),
                0,
            ),
            iop_trace!("poly0"),
        );

        // invoke sumcheck protocol on first protocol
        let ns0 = transcript.new_namespace(namespace, iop_trace!("first sumcheck protocol"));

        SimpleSumcheck::register_iop_structure(
            ns0,
            transcript,
            &SumcheckVerifierParameter {
                degree: verifier_parameter.degrees.0,
                evaluation_domain: verifier_parameter.evaluation_domain,
                summation_domain: verifier_parameter.summation_domain,
            },
        );

        // verifier send r1
        transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full]);
        transcript.submit_verifier_current_round(namespace, iop_trace!("r1"));

        // receive poly1
        transcript.receive_prover_current_round(
            namespace,
            ProverRoundMessageInfo::new(
                vec![verifier_parameter.degrees.1],
                0,
                0,
                verifier_parameter.evaluation_domain.size(),
                0,
            ),
            iop_trace!("poly1"),
        );

        // invoke sumcheck protocol on second protocol
        let ns1 = transcript.new_namespace(namespace, iop_trace!("second sumcheck protocol"));

        SimpleSumcheck::register_iop_structure(
            ns1,
            transcript,
            &SumcheckVerifierParameter {
                degree: verifier_parameter.degrees.1,
                evaluation_domain: verifier_parameter.evaluation_domain,
                summation_domain: verifier_parameter.summation_domain,
            },
        );
    }

    fn query_and_decide<O: RoundOracle<F>>(
        namespace: NameSpace,
        verifier_parameter: &Self::VerifierParameter,
        public_input: &Self::PublicInput,
        _oracle_refs: &Self::OracleRefs,
        sponge: &mut S,
        tramscript_messages: &mut MessagesCollection<&mut O, VerifierMessage<F>>,
    ) -> Result<Self::VerifierOutput, Error> {
        // which oracle we are using to sumcheck
        let poly0_ref =
            SumcheckOracleRef::new(*tramscript_messages.prover_message_as_ref(namespace, 0));
        let poly1_ref =
            SumcheckOracleRef::new(*tramscript_messages.prover_message_as_ref(namespace, 1));

        // get the r0, r1 we squeezed in commit phase
        let r0 = tramscript_messages.verifier_message(namespace, 0)[0]
            .clone()
            .try_into_field_elements()
            .expect("invalid verifier message type")
            .remove(0);
        let r1 = tramscript_messages.verifier_message(namespace, 1)[0]
            .clone()
            .try_into_field_elements()
            .expect("invalid verifier message type")
            .remove(0);

        let asserted_sums = (public_input.sums.0 * r0, public_input.sums.1 * r1);

        // invoke first sumcheck protocol
        let mut result = SimpleSumcheck::query_and_decide(
            tramscript_messages.get_subprotocol_namespace(namespace, 0),
            &SumcheckVerifierParameter {
                degree: verifier_parameter.degrees.0,
                evaluation_domain: verifier_parameter.evaluation_domain,
                summation_domain: verifier_parameter.summation_domain,
            },
            &SumcheckPublicInput::new(asserted_sums.0, 0),
            &poly0_ref,
            sponge,
            tramscript_messages,
        )?;

        // invoke second sumcheck protocol
        result &= SimpleSumcheck::query_and_decide(
            tramscript_messages.get_subprotocol_namespace(namespace, 1),
            &SumcheckVerifierParameter {
                degree: verifier_parameter.degrees.1,
                evaluation_domain: verifier_parameter.evaluation_domain,
                summation_domain: verifier_parameter.summation_domain,
            },
            &SumcheckPublicInput::new(asserted_sums.1, 0),
            &poly1_ref,
            sponge,
            tramscript_messages,
        )?;

        Ok(result)
    }
}

/// Multiround version of a simple univariate sumcheck (currently without ldt,
/// which is completely insecure). We assume that size of summation domain <
/// degree of testing poly < size of evaluation domain
#[test]
fn multiround_example() {
    let mut rng = test_rng();
    let degrees = (155, 197);
    let poly0 = DensePolynomial::<Fr>::rand(degrees.0, &mut rng);
    let poly1 = DensePolynomial::<Fr>::rand(degrees.1, &mut rng);
    let summation_domain = Radix2EvaluationDomain::new(64).unwrap();
    let evaluation_domain = Radix2EvaluationDomain::new(512).unwrap();
    let fri_parameters = FRIParameters::new(
        256,
        vec![1, 3, 1],
        Radix2CosetDomain::new(evaluation_domain, Fr::one()),
    );
    let ldt_parameter = LinearCombinationLDTParameters {
        fri_parameters,
        num_queries: 3,
    };
    let claimed_sum1 = Radix2CosetDomain::new(summation_domain.clone(), Fr::one())
        .evaluate(&poly0)
        .into_iter()
        .sum::<Fr>();
    let claimed_sum2 = Radix2CosetDomain::new(summation_domain.clone(), Fr::one())
        .evaluate(&poly1)
        .into_iter()
        .sum::<Fr>();

    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let mt_hash_parameters = MTHashParameters::<FieldMTConfig> {
        leaf_hash_param: poseidon_parameters(),
        inner_hash_param: poseidon_parameters(),
    };

    let vp = PublicInput {
        sums: (claimed_sum1, claimed_sum2),
    };
    let wp = PrivateInput(poly0, poly1);
    let prover_param = Parameter {
        degrees,
        summation_domain,
        evaluation_domain,
    };

    let proof = BCSProof::generate::<
        SumcheckMultiroundExample<Fr>,
        SumcheckMultiroundExample<Fr>,
        LinearCombinationLDT<Fr>,
        _,
    >(
        sponge,
        &vp,
        &wp,
        &prover_param,
        &ldt_parameter,
        mt_hash_parameters.clone(),
    )
    .expect("fail to generate proof");
    println!("Proof Size: {} bytes", proof.serialized_size());

    // Now let's verify if the proof is correct!

    let sponge = PoseidonSponge::new(&poseidon_parameters());

    let verifier_param = prover_param.to_verifier_param();
    let result = BCSVerifier::verify::<SumcheckMultiroundExample<Fr>, LinearCombinationLDT<Fr>, _>(
        sponge,
        &proof,
        &vp,
        &verifier_param,
        &ldt_parameter,
        mt_hash_parameters.clone(),
    )
    .expect("fail to verify");
    assert!(result);
    println!("verify result: ok!")
}
