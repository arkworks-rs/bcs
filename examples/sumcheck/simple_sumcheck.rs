use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_poly::{
    polynomial::univariate::DensePolynomial, univariate::DenseOrSparsePolynomial, EvaluationDomain,
    Polynomial, Radix2EvaluationDomain, UVPolynomial,
};
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::{marker::PhantomData, Zero};

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

pub struct SimpleSumcheck<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

#[derive(Clone)]
pub struct SumcheckPublicInput<F: PrimeField + Absorb> {
    claimed_sum: F,
    /// `SumcheckOracleRef` represents one round, which can contain multiple
    /// oracles. Which oracle do we want to look at?
    which: usize,
}

impl<F: PrimeField + Absorb> SumcheckPublicInput<F> {
    pub fn new(claimed_sum: F, which: usize) -> Self {
        SumcheckPublicInput { claimed_sum, which }
    }
}

#[derive(Clone, Debug, Copy)]
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
    /// Degree of the polynomial input
    pub degree: usize,
    /// evaluation domain
    pub evaluation_domain: Radix2EvaluationDomain<F>,
    /// summation domain
    pub summation_domain: Radix2EvaluationDomain<F>,
}

#[derive(Clone, Debug)]
pub struct SumcheckVerifierParameter<F: PrimeField> {
    /// Degree of the polynomial input
    pub degree: usize,
    /// evaluation domain
    pub evaluation_domain: Radix2EvaluationDomain<F>,
    /// summation domain
    pub summation_domain: Radix2EvaluationDomain<F>,
}

impl<F: PrimeField> ProverParam for SumcheckProverParameter<F> {
    type VerifierParameter = SumcheckVerifierParameter<F>;

    fn to_verifier_param(&self) -> Self::VerifierParameter {
        Self::VerifierParameter {
            degree: self.degree,
            evaluation_domain: self.evaluation_domain,
            summation_domain: self.summation_domain,
        }
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
        namespace: NameSpace,
        oracle_refs: &Self::RoundOracleRefs,
        public_input: &Self::PublicInput,
        _private_input: &Self::PrivateInput,
        transcript: &mut Transcript<MT, S, F>,
        prover_parameter: &Self::ProverParameter,
    ) -> Result<(), ark_bcs::Error>
    where
        MT::InnerDigest: Absorb,
    {
        // sanity check: `coeffs` in prover parameter matches the referenced oracle
        let actual_eval = &transcript
            .get_previously_sent_prover_round(oracle_refs.poly)
            .reed_solomon_codes()[public_input.which]
            .0;
        let expected_eval = prover_parameter
            .coeffs
            .clone()
            .evaluate_over_domain(prover_parameter.evaluation_domain)
            .evals;
        assert_eq!(&expected_eval, actual_eval);

        let (hx, gx) = prover_parameter
            .coeffs
            .divide_by_vanishing_poly(prover_parameter.summation_domain)
            .unwrap();
        let claim_sum_over_size = DensePolynomial::from_coefficients_vec(vec![
            public_input.claimed_sum / F::from(prover_parameter.summation_domain.size as u128),
        ]);
        let x = DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]);
        let (px, r) = DenseOrSparsePolynomial::from(gx + (-claim_sum_over_size))
            .divide_with_q_and_r(&DenseOrSparsePolynomial::from(x))
            .unwrap();
        // remainder should be zero
        assert!(r.is_zero());

        let hx_degree_bound =
            prover_parameter.degree - prover_parameter.summation_domain.size as usize;
        let px_degree_bound = prover_parameter.summation_domain.size as usize - 2;

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
    type VerifierParameter = SumcheckVerifierParameter<F>;
    /// SumcheckOracleRef contains the evaluation oracle for the poly to sum.
    type OracleRefs = SumcheckOracleRef;
    type PublicInput = SumcheckPublicInput<F>;

    fn register_iop_structure<MT: Config<Leaf = [F]>>(
        namespace: NameSpace,
        transcript: &mut SimulationTranscript<MT, S, F>,
        verifier_parameter: &Self::VerifierParameter,
    ) where
        MT::InnerDigest: Absorb,
    {
        let hx_degree_bound =
            verifier_parameter.degree - verifier_parameter.summation_domain.size as usize;
        let px_degree_bound = verifier_parameter.summation_domain.size as usize - 2;
        let expected_round_info = ProverRoundMessageInfo {
            num_message_oracles: 0,
            reed_solomon_code_degree_bound: vec![hx_degree_bound, px_degree_bound],
            oracle_length: verifier_parameter.evaluation_domain.size(),
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
        namespace: NameSpace,
        verifier_parameter: &Self::VerifierParameter,
        public_input: &Self::PublicInput,
        oracle_refs: &Self::OracleRefs, /* in parent `query_and_decide`, parent can fill out
                                         * this `oracle_refs` using the message in current
                                         * protocol */
        random_oracle: &mut S,
        transcript_messages: &mut MessagesCollection<O, VerifierMessage<F>>,
    ) -> Result<Self::VerifierOutput, Error> {
        // query a random point in evaluation domain
        let evaluation_domain = verifier_parameter.evaluation_domain;
        let summation_domain = verifier_parameter.summation_domain;
        let claimed_sum = public_input.claimed_sum;
        let evaluation_domain_log_size = evaluation_domain.log_size_of_group;
        let query = random_oracle
            .squeeze_bits(evaluation_domain_log_size as usize)
            .into_iter()
            .enumerate()
            .map(|(k, v)| (v as usize) << k)
            .sum::<usize>();
        let query_point = evaluation_domain.element(query);

        let query_responses = transcript_messages
            .prover_message(namespace, 0)
            .query(&[query], iop_trace!("sumcheck query"))
            .pop()
            .unwrap();
        let h_point = query_responses[0];
        let p_point = query_responses[1];
        let vh_point = query_point.pow(&[summation_domain.size]) - F::one(); // evaluate over vanishing poly

        // f(s)
        let expected = transcript_messages.prover_message_using_ref(oracle_refs.poly).query(&[query], iop_trace!("oracle access to poly in sumcheck"))
            .remove(0)// there's only one query, so always zero
            .remove(public_input.which); // we want to get `which` oracle in this round
                                         // h(s) * v_h(s) + (s * p(s) + claimed_sum/summation_domain.size)
        let actual: F = h_point * vh_point
            + (query_point * p_point + claimed_sum / F::from(summation_domain.size as u128));

        debug_assert_eq!(expected, actual);
        return Ok(expected == actual);
    }
}

#[cfg(feature = "r1cs")]
pub mod constraints {
    use ark_crypto_primitives::merkle_tree::{constraints::ConfigGadget, Config};
    use ark_ff::PrimeField;
    use ark_poly::EvaluationDomain;
    use ark_r1cs_std::{
        boolean::Boolean, eq::EqGadget, fields::fp::FpVar, prelude::FieldVar, uint64::UInt64,
    };
    use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
    use ark_sponge::{
        constraints::{AbsorbGadget, CryptographicSpongeVar, SpongeWithGadget},
        Absorb,
    };

    use ark_bcs::{
        bcs::{constraints::transcript::SimulationTranscriptVar, transcript::NameSpace},
        iop::{
            constraints::{
                message::{SuccinctRoundOracleVarView, VerifierMessageVar},
                IOPVerifierWithGadget,
            },
            message::{MessagesCollection, ProverRoundMessageInfo},
        },
    };

    use crate::simple_sumcheck::SimpleSumcheck;
    use ark_r1cs_std::R1CSVar;

    pub struct SumcheckPublicInputVar<CF: PrimeField + Absorb> {
        claimed_sum: FpVar<CF>,
        which: usize,
    }

    impl<CF: PrimeField + Absorb> SumcheckPublicInputVar<CF> {
        pub fn new(claimed_sum: FpVar<CF>, which: usize) -> Self {
            SumcheckPublicInputVar { claimed_sum, which }
        }
    }

    impl<CF: PrimeField + Absorb, S: SpongeWithGadget<CF>> IOPVerifierWithGadget<S, CF>
        for SimpleSumcheck<CF>
    {
        type VerifierOutputVar = Boolean<CF>;
        type PublicInputVar = SumcheckPublicInputVar<CF>;

        fn register_iop_structure_var<MT: Config, MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>>(
            namespace: NameSpace,
            transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
            verifier_parameter: &Self::VerifierParameter,
        ) -> Result<(), SynthesisError>
        where
            MT::InnerDigest: Absorb,
            MTG::InnerDigest: AbsorbGadget<CF>,
        {
            let hx_degree_bound =
                verifier_parameter.degree - verifier_parameter.summation_domain.size as usize;
            let px_degree_bound = verifier_parameter.summation_domain.size as usize - 2;
            let expected_round_info = ProverRoundMessageInfo {
                num_message_oracles: 0,
                reed_solomon_code_degree_bound: vec![hx_degree_bound, px_degree_bound],
                oracle_length: verifier_parameter.evaluation_domain.size(),
                num_short_messages: 0,
                localization_parameter: 0, // ignored
            };
            transcript.receive_prover_current_round(
                namespace,
                expected_round_info,
                iop_trace!("sumcheck hx, px"),
            )?;
            Ok(())
        }

        fn query_and_decide_var(
            _cs: ConstraintSystemRef<CF>,
            namespace: NameSpace,
            verifier_parameter: &Self::VerifierParameter,
            public_input: &Self::PublicInputVar,
            oracle_refs: &Self::OracleRefs,
            sponge: &mut S::Var,
            transcript_messages: &mut MessagesCollection<
                &mut SuccinctRoundOracleVarView<CF>,
                VerifierMessageVar<CF>,
            >,
        ) -> Result<Self::VerifierOutputVar, SynthesisError> {
            // // query a random point in evaluation domain
            let evaluation_domain = verifier_parameter.evaluation_domain;
            let summation_domain = verifier_parameter.summation_domain;
            let claimed_sum = public_input.claimed_sum.clone();
            let evaluation_domain_log_size = evaluation_domain.log_size_of_group;
            //
            let query = sponge
                .squeeze_bits(evaluation_domain_log_size as usize)?
                .into_iter()
                .collect::<Vec<_>>();
            let query_point = FpVar::constant(evaluation_domain.group_gen).pow_le(&query)?;

            let query_responses = transcript_messages
                .prover_message(namespace, 0)
                .query(&[query.clone()], iop_trace!("sumcheck query"))?
                .pop()
                .unwrap();
            let h_point = query_responses[0].clone();
            let p_point = query_responses[1].clone();
            let vh_point = query_point
                .pow_le(&UInt64::constant(summation_domain.size).to_bits_le())?
                - FpVar::constant(CF::one());

            // f(s)
            let expected = transcript_messages
                .prover_message_using_ref(oracle_refs.poly)
                .query(
                    &[query.clone()],
                    iop_trace!("oracle access to poly in sumcheck"),
                )?
                .remove(0)
                .remove(public_input.which);
            let actual = &h_point * &vh_point
                + &(&query_point * &p_point
                    + &claimed_sum
                        * &FpVar::constant(CF::from(summation_domain.size as u128)).inverse()?);

            assert_eq!(expected.value().unwrap(), actual.value().unwrap());
            return expected.is_eq(&actual);
        }
    }
}
