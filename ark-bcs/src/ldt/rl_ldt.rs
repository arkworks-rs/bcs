use crate::{
    bcs::{simulation_transcript::SimulationTranscript, transcript::Transcript},
    iop::{
        bookkeeper::{BookkeeperContainer, NameSpace},
        message::{MessagesCollection, MsgRoundRef, ProverRoundMessageInfo},
        oracles::RoundOracle,
    },
    ldt::LDT,
    Error,
};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_ldt::{
    direct::DirectLDT,
    domain::Radix2CosetDomain,
    fri::{prover::FRIProver, verifier::FRIVerifier, FRIParameters},
};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};
use ark_std::{marker::PhantomData, vec::Vec};
use tracing::Level;

/// Implementation of LDT using FRI protocol. When taking multiple oracles, this
/// protocol takes a random linear combination.
///
/// Each oracle message can have different degree bound, as long as its degree
/// bound <= tested_degree in FRI parameter. To enforce individual bound, this protocol follows [SCRSVP19](https://eprint.iacr.org/2018/) section 8, such that we
/// multiply each oracle by monimial x^{degree_to_raise} and take random linear
/// combination.
pub struct LinearCombinationLDT<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

#[derive(Clone)]
/// Parameter for Linear combination LDT, which includes parameter for FRI and
/// number of queries.
pub struct LinearCombinationLDTParameters<F: PrimeField + Absorb> {
    /// FRI parameter for the linearly combined polynomial
    pub fri_parameters: FRIParameters<F>,
    /// Number of FRI queries
    pub num_queries: usize,
}

impl<F: PrimeField + Absorb> LinearCombinationLDTParameters<F> {
    /// Create a new parameter for Linear Combination LDT
    pub fn new(
        max_degree_bound: u64,
        localization_param: Vec<u64>,
        codeword_domain: Radix2CosetDomain<F>,
        num_queries: usize,
    ) -> Self {
        LinearCombinationLDTParameters {
            fri_parameters: FRIParameters::new(
                max_degree_bound,
                localization_param,
                codeword_domain,
            ),
            num_queries,
        }
    }
}

impl<F: PrimeField + Absorb> LDT<F> for LinearCombinationLDT<F> {
    type LDTParameters = LinearCombinationLDTParameters<F>;

    fn codeword_domain(param: &Self::LDTParameters) -> Option<Radix2CosetDomain<F>> {
        Some(param.fri_parameters.domain)
    }

    fn localization_param(param: &Self::LDTParameters) -> Option<usize> {
        Some(param.fri_parameters.localization_parameters[0] as usize)
    }

    fn prove<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        namespace: NameSpace,
        param: &Self::LDTParameters,
        transcript: &mut Transcript<MT, S, F>,
        codewords: &[MsgRoundRef],
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb,
    {
        let span = tracing::span!(Level::INFO, "LDT Prove");
        let _enter = span.enter();
        let param = &param.fri_parameters;
        // get number of coefficients needed
        let num_oracles = codewords
            .iter()
            .map(|round| {
                transcript
                    .get_previously_sent_prover_round_info(*round)
                    .num_reed_solomon_codes_oracles()
            })
            .sum::<usize>();

        let random_coefficients = transcript.squeeze_verifier_field_elements(
            &(0..num_oracles)
                .map(|_| FieldElementSize::Full)
                .collect::<Vec<_>>(),
        );
        transcript.submit_verifier_current_round(namespace, iop_trace!("ldt random coefficeints"));

        let mut result_codewords = (0..param.domain.size())
            .map(|_| F::zero())
            .collect::<Vec<_>>();

        codewords
            .iter()
            .flat_map(|round| {
                let degrees_bounds = transcript
                    .get_previously_sent_prover_round_info(*round)
                    .reed_solomon_code_degree_bound;
                let rs_codes = transcript.get_previous_sent_prover_rs_codes(*round);
                assert_eq!(rs_codes.len(), degrees_bounds.len());
                // make sure degree_bounds degree is less than or equal to tested_degree
                assert!(degrees_bounds
                    .iter()
                    .all(|degree_bound| *degree_bound <= param.tested_degree as usize));
                rs_codes.into_iter().zip(degrees_bounds)
            })
            .zip(random_coefficients.iter())
            .for_each(|((oracle, degree), coeff)| {
                assert_eq!(oracle.len(), result_codewords.len());
                // if the degree bound of polynomial is less than tested degree, we
                // multiply the polynomial by x^{degree_to_raise}
                let degree_to_raise = param.tested_degree - degree as u64;
                let degree_raise_poly = degree_raise_poly_eval(param.domain, degree_to_raise);
                result_codewords
                    .iter_mut()
                    .zip(oracle.iter())
                    .zip(degree_raise_poly.iter())
                    .for_each(
                        |((r /* result */, a /* oracle */), d /* degree raise poly */)| {
                            *r += *coeff * *a * *d
                        },
                    )
            });

        let mut current_domain = param.domain;
        let mut current_evaluations = result_codewords;

        // generate FRI round oracles (first parameter is codeword)
        param.localization_parameters[0..param.localization_parameters.len() - 1]
            .iter()
            .zip(param.localization_parameters[1..param.localization_parameters.len()].iter())
            .try_for_each(
                |(&localization_current, &localization_next)| -> Result<(), Error> {
                    let alpha =
                        transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full])[0];
                    transcript.submit_verifier_current_round(namespace, iop_trace!("ldt alpha"));
                    let (next_domain, next_evaluations) = FRIProver::interactive_phase_single_round(
                        current_domain,
                        current_evaluations.clone(), /* TODO: change argument type to reference
                                                      * so we do not need to clone this */
                        localization_current,
                        alpha,
                    );
                    // prover send out this oracle evaluation as message
                    // each leaf will contain a coset
                    // transcript.send_message_oracle_with_localization(
                    //     next_evaluations.clone(),
                    //     localization_next as usize,
                    // )?;
                    // transcript
                    //     .submit_prover_current_round(namespace, iop_trace!("ldt fri oracle"))?;
                    transcript
                        .add_prover_round_with_custom_length_and_localization(
                            next_evaluations.len(),
                            localization_next as usize,
                        )
                        .send_oracle_message_without_degree_bound(next_evaluations.clone())
                        .submit(namespace, iop_trace!("ldt fri oracle"))?;

                    current_domain = next_domain;
                    current_evaluations = next_evaluations;
                    Ok(())
                },
            )?;
        // generate final polynomial
        let alpha = transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full])[0];
        transcript.submit_verifier_current_round(namespace, iop_trace!("ldt final alpha"));
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
        let sanity_check_point = final_polynomial_evaluations[1];
        let final_polynomial = DirectLDT::generate_low_degree_coefficients(
            domain_final,
            final_polynomial_evaluations,
            final_poly_degree_bound as usize,
        );
        // sanity check
        debug_assert_eq!(
            final_polynomial.evaluate(&domain_final.element(1)),
            sanity_check_point
        );
        assert!(final_polynomial.coeffs.len() <= (final_poly_degree_bound + 1) as usize);
        // transcript.send_message(final_polynomial.coeffs);
        // transcript
        //     .submit_prover_current_round(namespace, iop_trace!("ldt final poly
        // coefficients"))?;
        transcript
            .add_prover_round_with_custom_length_and_localization(0, 0)
            .send_short_message(final_polynomial.coeffs)
            .submit(namespace, iop_trace!("ldt final poly coefficients"))?;

        Ok(())
    }

    fn register_iop_structure<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        namespace: NameSpace,
        param: &Self::LDTParameters,
        num_codewords_oracles: usize,
        transcript: &mut SimulationTranscript<MT, S, F>,
    ) where
        MT::InnerDigest: Absorb,
    {
        let span = tracing::span!(Level::INFO, "ldt register");
        let _enter = span.enter();
        transcript.squeeze_verifier_field_elements(
            &(0..num_codewords_oracles)
                .map(|_| FieldElementSize::Full)
                .collect::<Vec<_>>(),
        );
        transcript
            .submit_verifier_current_round(namespace, iop_trace!("LDT random linear combination"));
        // prover generate result codewords
        let mut current_domain = param.fri_parameters.domain;

        // receive ldt message oracles
        param.fri_parameters.localization_parameters
            [0..param.fri_parameters.localization_parameters.len() - 1]
            .iter()
            .zip(param.fri_parameters.localization_parameters[1..].iter())
            .for_each(|(&localization_curr, &localization_next)| {
                transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full]);
                transcript.submit_verifier_current_round(namespace, iop_trace!("LDT alpha"));
                let next_domain = current_domain.fold(localization_curr);
                // ldt will receive a one oracle message
                transcript.receive_prover_current_round(
                    namespace,
                    // ProverRoundMessageInfo {
                    //     reed_solomon_code_degree_bound: Vec::default(), // none
                    //     num_message_oracles: 1,
                    //     num_short_messages: 0,
                    //     localization_parameter: localization_next as usize,
                    //     oracle_length: next_domain.size(),
                    // },
                    ProverRoundMessageInfo::new_using_custom_length_and_localization(
                        next_domain.size(),
                        localization_next as usize,
                    )
                    .with_num_message_oracles(1)
                    .build(),
                    iop_trace!("LDT prover message"),
                );

                current_domain = next_domain;
            });

        // receive final polynomials
        transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full]);
        transcript.submit_verifier_current_round(namespace, iop_trace!("LDT alpha for final"));
        transcript.receive_prover_current_round(
            namespace,
            // ProverRoundMessageInfo {
            //     reed_solomon_code_degree_bound: Vec::default(),
            //     num_message_oracles: 0,
            //     num_short_messages: 1,
            //     localization_parameter: 0, // ignored
            //     oracle_length: 0,          // ignored
            // },
            ProverRoundMessageInfo::new_using_custom_length_and_localization(0, 0)
                .with_num_short_messages(1)
                .build(),
            iop_trace!("LDT final polynomial"),
        );
    }

    // otherwise we have lifetime issue
    fn query_and_decide<S: CryptographicSponge, O: RoundOracle<F>>(
        namespace: NameSpace,
        param: &Self::LDTParameters,
        sponge: &mut S,
        codewords: &[MsgRoundRef], // TODO: codewords should include virtual codewords
        transcript_messages: &mut MessagesCollection<F, O>,
    ) -> Result<(), Error> {
        let span = tracing::span!(tracing::Level::INFO, "LDT Query");
        let _enter = span.enter();
        // calculate random coset indices for each query
        let codeword_log_num_cosets = param.fri_parameters.domain.dim()
            - param.fri_parameters.localization_parameters[0] as usize;
        let query_indices = (0..param.num_queries)
            .map(|_| le_bits_to_usize(&sponge.squeeze_bits(codeword_log_num_cosets)));
        // restore random coefficients and alphas
        let random_coefficients = transcript_messages.verifier_round((namespace, 0))[0]
            .clone()
            .try_into_field_elements()
            .unwrap();

        // verifier message from index 1 to num_alphas are alphas
        let alphas = (1..param.fri_parameters.localization_parameters.len() + 1).map(|i|
            // TODO: prover and verifier mismatches on this message
            transcript_messages.verifier_round((namespace, i))
        )
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
                    FRIVerifier::prepare_query(coset_index, &param.fri_parameters); // TODO: transcript need to to be passed into virtual oracles

                // get query responses in codewords oracles
                let mut codewords_oracle_responses = (0..query_cosets[0].size())
                    .map(|_| F::zero())
                    .collect::<Vec<_>>();

                codewords
                    .iter()
                    .flat_map(|oracle| {
                        let query_responses = transcript_messages
                            .prover_round(*oracle)
                            .query_coset(&[query_indices[0]], iop_trace!("rl_ldt query codewords"))
                            .assume_single_coset()
                            .into_iter()
                            .map(|round| round.into_iter());
                        let degrees = transcript_messages
                            .get_prover_round_info(*oracle)
                            .reed_solomon_code_degree_bound;
                        query_responses.zip(degrees.into_iter())
                    })
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
                assert_eq!(
                    transcript_messages.num_prover_rounds_in_namespace(namespace),
                    query_indices.len()
                );
                let round_oracle_responses = query_indices[1..]
                    .iter()
                    .zip(
                        transcript_messages
                            .prover_round_refs_in_namespace(namespace)
                            .clone()
                            .into_iter(),
                    )
                    .map(|(query_index, msg)| {
                        let mut response = transcript_messages
                            .prover_round(msg)
                            .query_coset(&[*query_index], iop_trace!("rl_ldt query fri message"))
                            .assume_single_coset(); // get the first coset position (only one position)
                        assert_eq!(response.len(), 1); // get the first oracle message in this round (only one message)
                        response.pop().unwrap()
                    })
                    .collect::<Vec<_>>();

                // get final polynomial coefficients
                let final_polynomial_coeffs = {
                    let &oracle_ref = transcript_messages
                        .prover_round_refs_in_namespace(namespace)
                        .last()
                        .unwrap();
                    transcript_messages
                        .prover_round(oracle_ref)
                        .short_message(0, iop_trace!("final poly coefficients"))
                }
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

                // TODO: do not panic. Use customized error
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
    // element h^{raise}(g^{index}^{raise}), h^{raise}(g^{index + dist *
    // 1}^{raise}), h^{raise}(g^{index + dist * 2}^{raise}), ...
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
    use crate::{
        bcs::{tests::FieldMTConfig, transcript::Transcript, MTHashParameters},
        iop::{bookkeeper::NameSpace, message::MessagesCollection},
        ldt::{
            rl_ldt::{
                degree_raise_poly_eval, degree_raise_poly_query, LinearCombinationLDT,
                LinearCombinationLDTParameters,
            },
            LDT,
        },
        test_utils::poseidon_parameters,
    };
    use ark_bls12_381::Fr;
    use ark_ldt::{domain::Radix2CosetDomain, fri::FRIParameters};
    use ark_poly::{
        domain::Radix2EvaluationDomain, polynomial::univariate::DensePolynomial, DenseUVPolynomial,
        EvaluationDomain,
    };
    use ark_sponge::{poseidon::PoseidonSponge, CryptographicSponge};
    use ark_std::{test_rng, vec, vec::Vec, One, Zero};

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

        for i in 0..8 {
            let poly = DensePolynomial::<Fr>::rand(69, &mut rng);
            let evaluation_domain = Radix2EvaluationDomain::new(256).unwrap();
            let fri_parameters = FRIParameters::new(
                128,
                vec![1, 2, 1],
                Radix2CosetDomain::new(evaluation_domain, Fr::one()),
            );
            let ldt_params = LinearCombinationLDTParameters {
                fri_parameters,
                num_queries: 1,
            };
            let root_namespace = NameSpace::root(iop_trace!("ldt test"));

            let mut sponge = PoseidonSponge::new(&poseidon_parameters());
            sponge.absorb(&i);
            let hash_params = MTHashParameters::<FieldMTConfig> {
                inner_hash_param: poseidon_parameters(),
                leaf_hash_param: poseidon_parameters(),
            };
            let mut transcript = Transcript::new(
                sponge,
                hash_params.clone(),
                LinearCombinationLDT::codeword_domain(&ldt_params),
                LinearCombinationLDT::localization_param(&ldt_params),
                iop_trace!("ldt test"),
            );
            // transcript
            //     .send_oracle_evaluations(poly.evaluate_over_domain(evaluation_domain).
            // evals, 69)     .unwrap();
            // transcript
            //     .submit_prover_current_round(root_namespace, iop_trace!())
            //     .unwrap();
            transcript
                .add_prover_round_with_codeword_domain()
                .send_oracle_evaluations_with_degree_bound(
                    poly.evaluate_over_domain(evaluation_domain).evals,
                    69,
                )
                .submit(root_namespace, iop_trace!())
                .unwrap();

            // check prove
            let ldt_namespace =
                transcript.new_namespace(root_namespace, iop_trace!("namespace for ldt"));
            let codewords = transcript.bookkeeper.dump_all_prover_messages_in_order();

            LinearCombinationLDT::prove(ldt_namespace, &ldt_params, &mut transcript, &codewords)
                .unwrap();

            // destruct transcript
            let mut sponge = transcript.sponge;

            let mut message_collection = MessagesCollection::new(
                transcript.prover_message_oracles,
                transcript
                    .registered_virtual_oracles
                    .into_iter()
                    .map(|v| Some(v.0))
                    .collect(),
                transcript.verifier_messages,
                transcript.bookkeeper,
            );

            LinearCombinationLDT::query_and_decide(
                ldt_namespace,
                &ldt_params,
                &mut sponge,
                &codewords,
                &mut message_collection,
            )
            .unwrap();

            // TODO: check restore
        }
    }
}
