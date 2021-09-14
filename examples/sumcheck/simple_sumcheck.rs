use ark_bcs::{
    bcs::transcript::{NameSpace, SimulationTranscript, Transcript},
    iop::{
        message::{
            MessagesCollection, MsgRoundRef, ProverRoundMessageInfo, RoundOracle, VerifierMessage,
        },
        prover::IOPProver,
        verifier::IOPVerifier,
        ProverOracleRefs, ProverParam,
    },
    Error,
};
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_poly::{
    polynomial::univariate::DensePolynomial, univariate::DenseOrSparsePolynomial, EvaluationDomain,
    Polynomial, Radix2EvaluationDomain, UVPolynomial,
};
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::{marker::PhantomData, Zero};

pub struct SimpleSumcheck<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

#[derive(Clone)]
pub struct SumcheckPublicInput<F: PrimeField + Absorb> {
    evaluation_domain: Radix2EvaluationDomain<F>,
    summation_domain: Radix2EvaluationDomain<F>,
    degree: usize,
    claimed_sum: F,
    /// `SumcheckOracleRef` represents one round, which can contain multiple
    /// oracles. Which oracle do we want to look at?
    which: usize,
}

impl<F: PrimeField + Absorb> SumcheckPublicInput<F> {
    pub fn new(
        evaluation_domain: Radix2EvaluationDomain<F>,
        summation_domain: Radix2EvaluationDomain<F>,
        degree: usize,
        claimed_sum: F,
        which: usize,
    ) -> Self {
        SumcheckPublicInput {
            evaluation_domain,
            summation_domain,
            degree,
            claimed_sum,
            which,
        }
    }
}

#[derive(Clone, Debug)]
pub struct SumcheckOracleRef {
    poly: MsgRoundRef,
}

impl SumcheckOracleRef {
    pub fn new(poly: MsgRoundRef) -> Self {
        SumcheckOracleRef { poly }
    }
}

#[derive(Clone, Debug)]
pub struct SumcheckProverParameter<F: PrimeField> {
    /// he coefficients corresponding to the `poly` in `SumcheckOracleRef`
    pub coeffs: DensePolynomial<F>,
}

impl<F: PrimeField> ProverParam for SumcheckProverParameter<F> {
    type VerifierParameter = ();

    fn to_verifier_param(&self) -> Self::VerifierParameter {
        ()
    }
}

impl ProverOracleRefs for SumcheckOracleRef {
    type VerifierOracleRefs = Self;

    fn to_verifier_oracle_refs(&self) -> Self::VerifierOracleRefs {
        self.clone()
    }
}

impl<F: PrimeField + Absorb> IOPProver<F> for SimpleSumcheck<F> {
    type ProverParameter = SumcheckProverParameter<F>;
    type RoundOracleRefs = SumcheckOracleRef;
    type PublicInput = SumcheckPublicInput<F>;
    type PrivateInput = ();

    fn prove<MT: Config<Leaf = [F]>, S: CryptographicSponge>(
        namespace: &NameSpace,
        oracle_refs: &Self::RoundOracleRefs,
        public_input: &Self::PublicInput,
        _private_input: &Self::PrivateInput,
        transcript: &mut Transcript<MT, S, F>,
        prover_parameter: &Self::ProverParameter,
    ) -> Result<(), ark_bcs::Error>
    where
        MT::InnerDigest: Absorb,
    {
        // TODO explain this more thoroughly
        // sanity check: `coeffs` in prover parameter matches the referenced oracle
        let actual_eval = &transcript
            .get_previously_sent_prover_round(oracle_refs.poly)
            .reed_solomon_codes()[public_input.which]
            .0;
        let expected_eval = prover_parameter
            .coeffs
            .clone()
            .evaluate_over_domain(public_input.evaluation_domain)
            .evals;
        assert_eq!(&expected_eval, actual_eval);

        let (hx, gx) = prover_parameter
            .coeffs
            .divide_by_vanishing_poly(public_input.summation_domain.clone())
            .unwrap();
        let claim_sum_over_size = DensePolynomial::from_coefficients_vec(vec![
            public_input.claimed_sum / F::from(public_input.summation_domain.size as u128),
        ]);
        let x = DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]);
        let (px, r) = DenseOrSparsePolynomial::from(gx + (-claim_sum_over_size))
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(x))
            .unwrap();
        // remainder should be zero
        assert!(r.is_zero());

        let hx_degree_bound = public_input.degree - public_input.summation_domain.size as usize;
        println!("hx: degree {}, bound {}", hx.degree(), hx_degree_bound);
        let px_degree_bound = public_input.summation_domain.size as usize - 1;
        println!("px: degree {}, bound {}", px.degree(), px_degree_bound);

        transcript.send_univariate_polynomial(hx_degree_bound, &hx)?;
        transcript.send_univariate_polynomial(px_degree_bound, &px)?;

        transcript.submit_prover_current_round(namespace, iop_trace!("sumcheck hx, px"))?;
        Ok(())
    }
}

impl<S: CryptographicSponge, F: PrimeField + Absorb> IOPVerifier<S, F> for SimpleSumcheck<F> {
    // in fact, we can output a subclaim (so verifier do not even need to access the
    // oracle!) but we keep it simple in this example
    type VerifierOutput = bool;
    type VerifierParameter = ();
    /// SumcheckOracleRef contains the evaluation oracle for the poly to sum.
    type OracleRefs = SumcheckOracleRef;
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
        transcript.receive_prover_current_round(
            namespace,
            expected_round_info,
            iop_trace!("sumcheck hx, px"),
        );
    }

    fn query_and_decide<O: RoundOracle<F>>(
        namespace: &NameSpace,
        _verifier_parameter: &Self::VerifierParameter,
        public_input: &Self::PublicInput,
        oracle_refs: &Self::OracleRefs, /* in parent `query_and_decide`, parent can fill out
                                         * this `oracle_refs` using the message in current
                                         * protocol */
        random_oracle: &mut S,
        messages_in_commit_phase: &mut MessagesCollection<&mut O, VerifierMessage<F>>,
    ) -> Result<Self::VerifierOutput, Error> {
        // // query a random point in evaluation domain
        let evaluation_domain = public_input.evaluation_domain;
        let summation_domain = public_input.summation_domain;
        let claimed_sum = public_input.claimed_sum;
        let evaluation_domain_log_size = evaluation_domain.log_size_of_group;
        let query = random_oracle
            .squeeze_bits(evaluation_domain_log_size as usize)
            .into_iter()
            .enumerate()
            .map(|(k, v)| (v as usize) << k)
            .sum::<usize>();
        let query_point = evaluation_domain.element(query);
        // // TODO: refactor this
        let queried_points = messages_in_commit_phase
            .prover_message(namespace, 0)
            .query(&[query], iop_trace!("sumcheck query"))
            .pop()
            .unwrap();
        let h_point = queried_points[0];
        let p_point = queried_points[1];
        let vh_point = summation_domain
            .vanishing_polynomial()
            .evaluate(&query_point);

        // f(s)
        let expected = messages_in_commit_phase.prover_message_using_ref(oracle_refs.poly).query(&[query], iop_trace!("oracle access to poly in sumcheck"))
            .remove(0)// there's only one query, so always zero
            .remove(public_input.which); // we want to get `which` oracle in this round
                                         // h(s) * v_h(s) + (s * p(s) + claimed_sum/summation_domain.size)
        let actual: F = h_point * vh_point
            + (query_point * p_point + claimed_sum / F::from(summation_domain.size as u128));

        debug_assert_eq!(expected, actual);
        return Ok(expected == actual);
    }
}
