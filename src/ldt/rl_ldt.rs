use crate::bcs::message::{
    ProverRoundMessageInfo, RoundOracle, SuccinctRoundOracleView, VerifierMessage,
};
use crate::bcs::transcript::{SimulationTranscript, Transcript, ROOT_NAMESPACE};
use crate::ldt::LDT;
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_ldt::direct::DirectLDT;
use ark_ldt::domain::Radix2CosetDomain;
use ark_ldt::fri::prover::FRIProver;
use ark_ldt::fri::verifier::FRIVerifier;
use ark_ldt::fri::FRIParameters;
use ark_poly::univariate::DensePolynomial;
use ark_poly::UVPolynomial;
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;

/// Implementation of LDT using FRI protocol. When taking multiple oracles, this protocol takes a random linear combination.
///
/// Each oracle message can have different degree bound, as long as its degree bound <= tested_degree in FRI parameter.
/// To enforce individual bound, this protocol follows [SCRSVP19](https://eprint.iacr.org/2018/) section 8, such that we
/// multiply each oracle by monimial x^{degree_to_raise} and take random linear combination.
///
pub struct LinearCombinationFRI<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

#[derive(Clone)]
pub struct LinearCombinationFRIParameters<F: PrimeField + Absorb> {
    /// FRI parameter for the linearly combined polynomial
    pub fri_parameters: FRIParameters<F>,
    /// Number of FRI queries
    pub num_queries: usize,
}

impl<F: PrimeField + Absorb> LDT<F> for LinearCombinationFRI<F> {
    type LDTParameters = LinearCombinationFRIParameters<F>;

    fn ldt_info(
        param: &Self::LDTParameters,
        _degree_bound: usize,
    ) -> (Radix2CosetDomain<F>, usize) {
        let param = &param.fri_parameters;
        let codeword_localization = param.localization_parameters[0];
        let codeword_domain = param.domain;
        (codeword_domain, codeword_localization as usize)
    }

    fn prove<'a, MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        param: &Self::LDTParameters,
        codewords: impl IntoIterator<Item = &'a Vec<(Vec<F>, usize)>>,
        ldt_transcript: &mut Transcript<MT, S, F>,
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb,
    {
        let param = &param.fri_parameters;
        let namespace = &ROOT_NAMESPACE; // TODO: fix this
                                         // first, get random linear combination of the codewords
        let codewords = codewords.into_iter().collect::<Vec<_>>();
        // get number of coefficients needed
        let num_oracles: usize = codewords.iter().map(|round| round.len()).sum();
        let random_coefficients = ldt_transcript.squeeze_verifier_field_elements(
            &(0..num_oracles)
                .map(|_| FieldElementSize::Full)
                .collect::<Vec<_>>(),
        );
        ldt_transcript
            .submit_verifier_current_round(&ROOT_NAMESPACE, iop_trace!("ldt random coefficeints"));

        let mut result_codewords = (0..param.domain.size())
            .map(|_| F::zero())
            .collect::<Vec<_>>();
        codewords
            .into_iter()
            .map(|round: &'a Vec<(Vec<F>, usize)>| {
                round.iter().map(|(evaluation, degree_bound)| {
                    assert!(
                        *degree_bound <= param.tested_degree as usize,
                        "degree bound larger than testing degree"
                    );
                    (evaluation, degree_bound)
                })
            })
            .flatten()
            .zip(random_coefficients.iter())
            .for_each(|((oracle, degree), coeff)| {
                assert_eq!(oracle.len(), result_codewords.len());
                // if the degree bound of polynomial is less than tested degree, we
                // multiply the polynomial by x^{degree_to_raise}
                let degree_to_raise = param.tested_degree - *degree as u64;
                let degree_raise_poly = degree_raise_poly_eval(param.domain, degree_to_raise);
                result_codewords
                    .iter_mut()
                    .zip(oracle.iter())
                    .zip(degree_raise_poly.iter())
                    .for_each(|((r /*result*/, a /*oracle*/), d /*degree raise poly*/)| {
                        *r += *coeff * *a * *d
                    })
            });

        let mut current_domain = param.domain;
        let mut current_evaluations = result_codewords;

        // generate FRI round oracles (first parameter is codeword)
        param.localization_parameters[0..param.localization_parameters.len() - 1]
            .iter()
            .zip(param.localization_parameters[1..param.localization_parameters.len()].iter())
            .try_for_each(
                |(&localization_current, &localization_next)| -> Result<(), Error> {
                    let alpha = ldt_transcript
                        .squeeze_verifier_field_elements(&[FieldElementSize::Full])[0];
                    ldt_transcript
                        .submit_verifier_current_round(namespace, iop_trace!("ldt alpha"));
                    let (next_domain, next_evaluations) = FRIProver::interactive_phase_single_round(
                        current_domain,
                        current_evaluations.clone(), // TODO: change argument type to reference so we do not need to clone this
                        localization_current,
                        alpha,
                    );
                    // prover send out this oracle evaluation as message
                    // each leaf will contain a coset
                    ldt_transcript.send_message_oracle_with_localization(
                        next_evaluations.clone(),
                        localization_next as usize,
                    )?;
                    ldt_transcript
                        .submit_prover_current_round(namespace, iop_trace!("ldt fri oracle"))?;

                    current_domain = next_domain;
                    current_evaluations = next_evaluations;
                    Ok(())
                },
            )?;

        // generate final polynomial
        let alpha = ldt_transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full])[0];
        ldt_transcript.submit_verifier_current_round(namespace, iop_trace!("ldt final alpha"));
        let (domain_final, final_polynomial_evaluations) =
            FRIProver::interactive_phase_single_round(
                current_domain,
                current_evaluations,
                *(param.localization_parameters.last().unwrap()),
                alpha,
            );
        // send final polynomial, which is not an oracle.
        // We send interpolated final polynomial coefficients instead of evaluations.
        let total_shrink_factor = param.localization_parameters.iter().sum::<u64>();
        let final_poly_degree_bound = param.tested_degree >> total_shrink_factor;
        let final_polynomial = DirectLDT::generate_low_degree_coefficients(
            domain_final,
            final_polynomial_evaluations,
            final_poly_degree_bound as usize,
        );
        assert!(final_polynomial.coeffs.len() <= (final_poly_degree_bound + 1) as usize);
        ldt_transcript.send_message(final_polynomial.coeffs);
        ldt_transcript
            .submit_prover_current_round(namespace, iop_trace!("ldt final poly coefficients"))?;

        Ok(())
    }

    fn restore_from_commit_phase<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        params: &Self::LDTParameters,
        codewords_oracles: Vec<&mut SuccinctRoundOracleView<F>>,
        ldt_transcript: &mut SimulationTranscript<MT, S, F>,
    ) where
        MT::InnerDigest: Absorb,
    {
        let namespace = &ROOT_NAMESPACE;
        let num_oracles = codewords_oracles
            .iter()
            .map(|round| round.oracle.info.num_oracles())
            .sum::<usize>();
        ldt_transcript.squeeze_verifier_field_elements(
            &(0..num_oracles)
                .map(|_| FieldElementSize::Full)
                .collect::<Vec<_>>(),
        );
        ldt_transcript.submit_verifier_current_round(&ROOT_NAMESPACE);
        // prover generate result codewords
        let mut current_domain = params.fri_parameters.domain;

        // receive ldt message oracles
        params.fri_parameters.localization_parameters
            [0..params.fri_parameters.localization_parameters.len() - 1]
            .iter()
            .zip(params.fri_parameters.localization_parameters[1..].iter())
            .for_each(|(&localization_curr, &localization_next)| {
                ldt_transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full]);
                ldt_transcript.submit_verifier_current_round(namespace);
                let next_domain = current_domain.fold(localization_curr);
                // ldt will receive a one oracle message
                ldt_transcript.receive_prover_current_round(
                    namespace,
                    ProverRoundMessageInfo {
                        reed_solomon_code_degree_bound: Vec::default(), // none
                        num_message_oracles: 1,
                        num_short_messages: 0,
                        localization_parameter: localization_next as usize,
                        oracle_length: next_domain.size(),
                    },
                );

                current_domain = next_domain;
            });

        // receive final polynomials
        ldt_transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full]);
        ldt_transcript.submit_verifier_current_round(namespace);
        ldt_transcript.receive_prover_current_round(
            namespace,
            ProverRoundMessageInfo {
                reed_solomon_code_degree_bound: Vec::default(),
                num_message_oracles: 0,
                num_short_messages: 1,
                localization_parameter: 0, // ignored
                oracle_length: 0,          // ignored
            },
        )
    }

    fn query_and_decide<S: CryptographicSponge, O: RoundOracle<F>>(
        param: &Self::LDTParameters,
        random_oracle: &mut S,
        mut codewords_oracles: Vec<&mut O>,
        mut ldt_prover_message_oracles: Vec<&mut O>,
        ldt_verifier_messages: &[Vec<VerifierMessage<F>>],
    ) -> Result<(), Error> {
        // calculate random coset indices for each query
        let codeword_log_num_cosets = param.fri_parameters.domain.dim()
            - param.fri_parameters.localization_parameters[0] as usize;
        let query_indices = (0..param.num_queries)
            .map(|_| le_bits_to_usize(&random_oracle.squeeze_bits(codeword_log_num_cosets)))
            .collect::<Vec<_>>();

        // restore random coefficients and alphas
        let random_coefficients = ldt_verifier_messages[0][0]
            .clone()
            .try_into_field_elements()
            .unwrap();

        let alphas = ldt_verifier_messages[1..]
            .iter()
            .map(|vm| {
                assert_eq!(vm.len(), 1);
                let vm_curr = vm[0] // each round have one message
                    .clone()
                    .try_into_field_elements()
                    .unwrap();
                assert_eq!(vm_curr.len(), 1);
                vm_curr[0]
            }) // each message is only one field element (alpha)
            .collect::<Vec<_>>();

        query_indices
            .into_iter()
            .try_for_each(|coset_index| -> Result<(), Error> {
                // prepare query
                let (query_cosets, query_indices, domain_final) =
                    FRIVerifier::prepare_query(coset_index, &param.fri_parameters);

                // get query responses in codewords oracles
                let mut codewords_oracle_responses = (0..query_cosets[0].size())
                    .map(|_| F::zero())
                    .collect::<Vec<_>>();

                codewords_oracles
                    .iter_mut()
                    .map(|oracle| {
                        let query_responses = oracle
                            .query_coset(&[query_indices[0]], iop_trace!("rl_ldt query codewords"))
                            .pop()
                            .unwrap()
                            .into_iter()
                            .map(|round| round.into_iter());
                        let degrees = oracle.get_degree_bound();
                        query_responses.zip(degrees.into_iter())
                    })
                    .flatten()
                    .zip(random_coefficients.iter())
                    .for_each(|((msg, degree_bound), coeff)| {
                        assert_eq!(codewords_oracle_responses.len(), msg.len());
                        assert!(param.fri_parameters.tested_degree > degree_bound as u64);
                        let degree_raise_poly_at_coset = degree_raise_poly_query(
                            param.fri_parameters.domain,
                            param.fri_parameters.tested_degree - degree_bound as u64,
                            param.fri_parameters.localization_parameters[0],
                            query_indices[0] as u64,
                        );
                        debug_assert_eq!(
                            codewords_oracle_responses.len(),
                            degree_raise_poly_at_coset.len()
                        );
                        codewords_oracle_responses
                            .iter_mut()
                            .zip(msg.into_iter().zip(degree_raise_poly_at_coset.into_iter()))
                            .for_each(|(dst, (src_oracle, src_raise))| {
                                *dst += *coeff * src_oracle * src_raise
                            })
                    });

                // get query responses in ldt prover messages oracles
                assert_eq!(ldt_prover_message_oracles.len(), query_indices.len());
                let round_oracle_responses = query_indices[1..]
                    .iter()
                    .zip(ldt_prover_message_oracles.iter_mut())
                    .map(|(query_index, msg)| {
                        let mut response = msg
                            .query_coset(&[*query_index], iop_trace!("rl_ldt query fri message"))
                            .pop()
                            .unwrap(); // get the first coset position (only one position)
                        assert_eq!(response.len(), 1); // get the first oracle message in this round (only one message)
                        response.pop().unwrap()
                    })
                    .collect::<Vec<_>>();

                // get final polynomial coefficients
                let final_polynomial_coeffs = ldt_prover_message_oracles
                    .last()
                    .unwrap()
                    .get_short_message(0, iop_trace!("final poly coefficient"))
                    .to_vec();
                let total_shrink_factor = param
                    .fri_parameters
                    .localization_parameters
                    .iter()
                    .sum::<u64>();
                let final_poly_degree_bound =
                    param.fri_parameters.tested_degree >> total_shrink_factor;
                // make sure final polynomial degree is valid
                assert!(final_polynomial_coeffs.len() <= (final_poly_degree_bound + 1) as usize);
                // todo!(): generate_low_degree_coefficients should be done by prover instead!
                let final_polynomial =
                    DensePolynomial::from_coefficients_vec(final_polynomial_coeffs);
                let result = FRIVerifier::consistency_check(
                    &param.fri_parameters,
                    &query_indices,
                    &query_cosets,
                    &ark_std::iter::once(codewords_oracle_responses)
                        .chain(round_oracle_responses.into_iter())
                        .collect::<Vec<_>>(),
                    &alphas,
                    &domain_final,
                    &final_polynomial,
                );

                // TODO: do not panic. Use error
                assert!(result);

                Ok(())
            })
    }
}

fn le_bits_to_usize(bits: &[bool]) -> usize {
    bits.iter()
        .enumerate()
        .map(|(pos, bit)| (*bit as usize) << pos)
        .sum()
}

// return evaluation of x^{degree_to_raise} at domain
// TODO: we need one test for this function
fn degree_raise_poly_eval<F: PrimeField>(
    domain: Radix2CosetDomain<F>,
    degree_to_raise: u64,
) -> Vec<F> {
    let mut result = Vec::with_capacity(domain.size());
    let mut curr = domain.offset.pow(&[degree_to_raise]);
    for _ in 0..domain.size() {
        result.push(curr);
        curr *= domain.gen().pow(&[degree_to_raise]);
    }
    result
}

// return evaluation of x^{degree_to_raise} at specific location
fn degree_raise_poly_query<F: PrimeField>(
    domain: Radix2CosetDomain<F>,
    degree_to_raise: u64,
    log_coset_size: u64,
    coset_index: u64,
) -> Vec<F> {
    let mut result = Vec::with_capacity(1 << log_coset_size);
    let dist_between_coset_elems = 1 << (domain.dim() - log_coset_size as usize);
    // element h^{raise}(g^{index}^{raise}), h^{raise}(g^{index + dist * 1}^{raise}), h^{raise}(g^{index + dist * 2}^{raise}), ...
    let mut curr = domain.offset.pow(&[degree_to_raise])
        * domain.gen().pow(&[coset_index]).pow(&[degree_to_raise]);
    let step = domain
        .gen()
        .pow(&[dist_between_coset_elems])
        .pow(&[degree_to_raise]);
    for _ in 0..(1 << log_coset_size) {
        result.push(curr);
        curr *= step;
    }
    result
}

#[cfg(test)]
mod tests {
    use crate::bcs::tests::FieldMTConfig;
    use crate::bcs::transcript::{SimulationTranscript, Transcript, ROOT_NAMESPACE};
    use crate::bcs::MTHashParameters;
    use crate::ldt::rl_ldt::{
        degree_raise_poly_eval, degree_raise_poly_query, LinearCombinationFRI,
        LinearCombinationFRIParameters,
    };
    use crate::ldt::LDT;
    use crate::test_utils::poseidon_parameters;
    use ark_bls12_381::Fr;
    use ark_ldt::domain::Radix2CosetDomain;
    use ark_ldt::fri::FRIParameters;
    use ark_poly::domain::Radix2EvaluationDomain;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly::{EvaluationDomain, UVPolynomial};
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_sponge::CryptographicSponge;
    use ark_std::{test_rng, One, Zero};

    #[test]
    fn test_degree_raise_poly() {
        let domain = Radix2CosetDomain::new_radix2_coset(64, Fr::from(123456u128));
        // x^17
        let poly = DensePolynomial::from_coefficients_vec(
            (0..17)
                .map(|_| Fr::zero())
                .chain(ark_std::iter::once(Fr::one()))
                .collect(),
        );
        let expected_eval = domain.evaluate(&poly);
        let actual_eval = degree_raise_poly_eval(domain, 17);
        assert_eq!(expected_eval, actual_eval);

        let (queries, _) = domain.query_position_to_coset(3, 2);
        let expected_ans = queries.iter().map(|&i| actual_eval[i]).collect::<Vec<_>>();
        let actual_ans = degree_raise_poly_query(domain, 17, 2, 3);

        assert_eq!(expected_ans, actual_ans)
    }

    #[test]
    fn ldt_test() {
        let mut rng = test_rng();

        for i in 0..256 {
            let poly = DensePolynomial::<Fr>::rand(69, &mut rng);
            let evaluation_domain = Radix2EvaluationDomain::new(256).unwrap();
            let fri_parameters = FRIParameters::new(
                128,
                vec![1, 2, 1],
                Radix2CosetDomain::new(evaluation_domain, Fr::one()),
            );
            let ldt_params = LinearCombinationFRIParameters {
                fri_parameters,
                num_queries: 1,
            };

            let mut sponge = PoseidonSponge::new(&poseidon_parameters());
            sponge.absorb(&i);
            let hash_params = MTHashParameters::<FieldMTConfig> {
                inner_hash_param: poseidon_parameters(),
                leaf_hash_param: poseidon_parameters(),
            };
            let mut transcript = Transcript::new(sponge, hash_params.clone(), |usize| {
                LinearCombinationFRI::ldt_info(&ldt_params, usize)
            });
            transcript
                .send_oracle_evaluations(
                    poly.evaluate_over_domain(evaluation_domain).evals,
                    69,
                    Radix2CosetDomain::new(evaluation_domain, Fr::one()),
                )
                .unwrap();
            transcript
                .submit_prover_current_round(&ROOT_NAMESPACE, iop_trace!())
                .unwrap();

            // check LDT
            let mut sponge_before_ldt = transcript.sponge;
            let mut ldt_transcript =
                Transcript::new(sponge_before_ldt.clone(), hash_params.clone(), |_| {
                    panic!("ldt not allowed")
                });
            LinearCombinationFRI::prove(
                &ldt_params,
                transcript
                    .prover_message_oracles
                    .iter()
                    .map(|round| &round.reed_solomon_codes),
                &mut ldt_transcript,
            )
            .unwrap();

            LinearCombinationFRI::query_and_decide(
                &ldt_params,
                &mut ldt_transcript.sponge,
                transcript.prover_message_oracles.iter_mut().collect(),
                ldt_transcript.prover_message_oracles.iter_mut().collect(),
                ldt_transcript.verifier_messages.as_slice(),
            )
            .unwrap();

            // check restore
            let ldt_message_oracle = ldt_transcript
                .prover_message_oracles
                .iter()
                .map(|round| round.get_succinct_oracle())
                .collect::<Vec<_>>();
            let ldt_message_mt_roots = ldt_transcript
                .merkle_tree_for_each_round
                .iter()
                .map(|tree| tree.as_ref().map(|t| t.root()))
                .collect::<Vec<_>>();
            let mut simulation_transcript = SimulationTranscript::from_prover_messages(
                &ldt_message_oracle,
                &ldt_message_mt_roots,
                &mut sponge_before_ldt,
                |_| panic!(),
            );

            let codewords_oracle = transcript
                .prover_message_oracles
                .iter()
                .map(|round| round.get_succinct_oracle())
                .collect::<Vec<_>>();
            let mut codewords_oracle_view = codewords_oracle
                .iter()
                .map(|r| r.get_view())
                .collect::<Vec<_>>();
            LinearCombinationFRI::restore_from_commit_phase(
                &ldt_params,
                codewords_oracle_view.iter_mut().collect(),
                &mut simulation_transcript,
            );

            simulation_transcript.check_correctness(&ldt_transcript);
        }
    }
}
