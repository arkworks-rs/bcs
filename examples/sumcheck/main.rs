mod test_utils;

#[macro_use]
extern crate ark_bcs;

use crate::test_utils::{poseidon_parameters, FieldMTConfig};
use ark_bcs::bcs::message::{ProverRoundMessageInfo, RoundOracle, VerifierMessage};
use ark_bcs::bcs::prover::BCSProof;
use ark_bcs::bcs::transcript::{MessageBookkeeper, NameSpace, SimulationTranscript, Transcript};
use ark_bcs::bcs::verifier::BCSVerifier;
use ark_bcs::bcs::MTHashParameters;
use ark_bcs::iop::prover::IOPProver;
use ark_bcs::iop::verifier::IOPVerifier;
use ark_bcs::ldt::rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters};
use ark_bcs::Error;
use ark_bls12_381::fr::Fr;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_ldt::fri::FRIParameters;
use ark_poly::univariate::{DenseOrSparsePolynomial, DensePolynomial};
use ark_poly::{EvaluationDomain, Polynomial, Radix2EvaluationDomain, UVPolynomial};
use ark_serialize::CanonicalSerialize;
use ark_sponge::poseidon::PoseidonSponge;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::marker::PhantomData;
use ark_std::{test_rng, One, Zero};

pub struct SimpleSumcheckProver<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

pub struct SimpleSumcheckVerifier<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

#[derive(Clone)]
pub struct SumcheckPublicInput<F: PrimeField + Absorb> {
    evaluation_domain: Radix2EvaluationDomain<F>,
    summation_domain: Radix2EvaluationDomain<F>,
    degree: usize,
    claimed_sum: F,
}

#[derive(Clone)]
pub struct SumcheckProverState<F: PrimeField + Absorb> {
    poly: DensePolynomial<F>,
    vp: SumcheckPublicInput<F>,
}

impl<F: PrimeField + Absorb> IOPProver<F> for SimpleSumcheckProver<F> {
    type ProverParameter = DensePolynomial<F>;
    type ProverState = SumcheckProverState<F>;
    type PublicInput = SumcheckPublicInput<F>;
    type PrivateInput = ();

    fn initial_state(
        params: &Self::ProverParameter,
        public_input: &Self::PublicInput,
        _private_input: &Self::PrivateInput,
    ) -> Self::ProverState {
        SumcheckProverState {
            poly: params.clone(),
            vp: public_input.clone(),
        }
    }

    fn prove<MT: Config<Leaf = [F]>, S: CryptographicSponge>(
        namespace: &NameSpace,
        state: &mut Self::ProverState,
        transcript: &mut Transcript<MT, S, F>,
        _prover_parameter: &Self::ProverParameter,
    ) -> Result<(), ark_bcs::Error>
    where
        MT::InnerDigest: Absorb,
    {
        // from lecture
        let (hx, gx) = state
            .poly
            .divide_by_vanishing_poly(state.vp.summation_domain.clone())
            .unwrap();
        let claim_sum_over_size = DensePolynomial::from_coefficients_vec(vec![
            state.vp.claimed_sum / F::from(state.vp.summation_domain.size as u128),
        ]);
        let x = DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]);
        let (px, r) = DenseOrSparsePolynomial::from(gx + (-claim_sum_over_size))
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(x))
            .unwrap();
        // remainder should be zero
        assert!(r.is_zero());

        let hx_degree_bound = state.vp.degree - state.vp.summation_domain.size as usize;
        println!("hx: degree {}, bound {}", hx.degree(), hx_degree_bound);
        let px_degree_bound = state.vp.summation_domain.size as usize - 1;
        println!("px: degree {}, bound {}", px.degree(), px_degree_bound);

        transcript.send_univariate_polynomial(hx_degree_bound, &hx)?;
        transcript.send_univariate_polynomial(px_degree_bound, &px)?;

        transcript.submit_prover_current_round(namespace, iop_trace!("sumcheck hx, px"))?;
        Ok(())
    }
}

impl<S: CryptographicSponge, F: PrimeField + Absorb> IOPVerifier<S, F>
    for SimpleSumcheckVerifier<F>
{
    type VerifierOutput = bool; // in real case, we can output a subclaim
    /// For simplicity, we let verifier own the testing polynomial, but in practice it only has oracle access.
    /// (When having oracle access, testing polynomial need to have same evaluation domain as current round.)
    type VerifierParameter = DensePolynomial<F>;
    type VerifierState = (Self::PublicInput, DensePolynomial<F>);
    type PublicInput = SumcheckPublicInput<F>;

    fn restore_from_commit_phase<MT: Config<Leaf = [F]>>(
        namespace: &NameSpace,
        public_input: &Self::PublicInput,
        transcript: &mut SimulationTranscript<MT, S, F>,
        _verifier_parameter: &Self::VerifierParameter,
    ) where
        MT::InnerDigest: Absorb,
    {
        let hx_degree_bound = public_input.degree - public_input.summation_domain.size as usize;
        let px_degree_bound = public_input.summation_domain.size as usize - 1;
        let expected_round_info = ProverRoundMessageInfo {
            num_message_oracles: 0,
            reed_solomon_code_degree_bound: vec![hx_degree_bound, px_degree_bound],
            oracle_length: public_input.evaluation_domain.size(),
            num_short_messages: 0,
            localization_parameter: 0, // ignored
        };
        transcript.receive_prover_current_round(namespace, expected_round_info);
    }

    fn initial_state_for_query_and_decision_phase(
        params: &Self::VerifierParameter,
        public_input: &Self::PublicInput,
    ) -> Self::VerifierState {
        (public_input.clone(), params.clone())
    }

    fn query_and_decide<O: RoundOracle<F>>(
        namespace: &NameSpace,
        _verifier_parameter: &Self::VerifierParameter,
        verifier_state: &mut Self::VerifierState,
        random_oracle: &mut S,
        mut prover_message_oracle: Vec<&mut O>,
        _verifier_messages: &[Vec<VerifierMessage<F>>],
        bookkeeper: &MessageBookkeeper,
    ) -> Result<Self::VerifierOutput, Error> {
        // query a random location in evaluation domain
        let evaluation_domain = verifier_state.0.evaluation_domain;
        let summation_domain = verifier_state.0.summation_domain;
        let claimed_sum = verifier_state.0.claimed_sum;
        let evaluation_domain_log_size = evaluation_domain.log_size_of_group;
        let query = random_oracle
            .squeeze_bits(evaluation_domain_log_size as usize)
            .into_iter()
            .enumerate()
            .map(|(k, v)| (v as usize) << k)
            .sum::<usize>();
        let query_point = evaluation_domain.element(query);

        let prover_current_oracles_indices =
            bookkeeper.get_prover_message_oracle_indices_in_namespace(namespace);
        let queried_points = prover_message_oracle[prover_current_oracles_indices[0]]
            .query(&[query], iop_trace!("sumcheck query"))
            .pop()
            .unwrap();
        let h_point = queried_points[0];
        let p_point = queried_points[1];
        let vh_point = summation_domain
            .vanishing_polynomial()
            .evaluate(&query_point);

        let expected = verifier_state.1.evaluate(&query_point);
        let actual = h_point * vh_point
            + (query_point * p_point + claimed_sum / F::from(summation_domain.size as u128));

        debug_assert_eq!(expected, actual);
        return Ok(expected == actual);
    }
}

/// A simple univariate sumcheck (currently without ldt, which is completely insecure).
/// We assume that size of summation domain < degree of testing poly < size of evaluation domain
fn main() {
    let mut rng = test_rng();
    let poly = DensePolynomial::<Fr>::rand(69, &mut rng);
    let summation_domain = Radix2EvaluationDomain::new(64).unwrap();
    let evaluation_domain = Radix2EvaluationDomain::new(256).unwrap();
    let fri_parameters = FRIParameters::new(
        128,
        vec![1, 3, 1],
        Radix2CosetDomain::new(evaluation_domain, Fr::one()),
    );
    let ldt_parameter = LinearCombinationLDTParameters {
        fri_parameters,
        num_queries: 3,
    };
    let claimed_sum: Fr = Radix2CosetDomain::new(summation_domain.clone(), Fr::one())
        .evaluate(&poly)
        .into_iter()
        .sum();

    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let mt_hash_parameters = MTHashParameters::<FieldMTConfig> {
        leaf_hash_param: poseidon_parameters(),
        inner_hash_param: poseidon_parameters(),
    };

    let testing_poly = poly.clone();
    let vp = SumcheckPublicInput {
        summation_domain,
        degree: 69,
        evaluation_domain: evaluation_domain.clone(),
        claimed_sum,
    };

    let proof = BCSProof::generate::<
        SimpleSumcheckVerifier<Fr>,
        SimpleSumcheckProver<Fr>,
        LinearCombinationLDT<Fr>,
        _,
    >(
        sponge,
        &vp,
        &(),
        &testing_poly,
        &testing_poly,
        &ldt_parameter,
        mt_hash_parameters.clone(),
    )
    .expect("fail to generate proof");

    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let verifier_output =
        BCSVerifier::verify::<SimpleSumcheckVerifier<Fr>, LinearCombinationLDT<Fr>, _>(
            sponge,
            &proof,
            &vp,
            &testing_poly,
            &ldt_parameter,
            mt_hash_parameters,
        )
        .expect("fail to verify proof");

    // for now verifier output is just a simple boolean. In real scenario, verifier can output a subclaim if it does not have
    // direct access to testing polynomial.
    assert!(verifier_output);
    println!("success");

    let proof_size = proof.serialized_size();
    println!("proof size: {} bytes", proof_size);
}
