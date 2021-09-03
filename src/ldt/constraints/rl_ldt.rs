use crate::bcs::constraints::message::{SuccinctRoundOracleVarView, VerifierMessageVar};
use crate::bcs::constraints::transcript::SimulationTranscriptVar;
use crate::bcs::message::ProverRoundMessageInfo;
use crate::bcs::transcript::ROOT_NAMESPACE;
use crate::ldt::constraints::LDTWithGadget;
use crate::ldt::rl_ldt::LinearCombinationLDT;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_ldt::fri::constraints::FRIVerifierGadget;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::poly::polynomial::univariate::dense::DensePolynomialVar;
use ark_relations::r1cs::SynthesisError;
use ark_sponge::constraints::{AbsorbGadget, CryptographicSpongeVar, SpongeWithGadget};
use ark_sponge::Absorb;

impl<F: PrimeField + Absorb> LDTWithGadget<F> for LinearCombinationLDT<F> {
    fn restore_from_commit_phase_var<MT, MTG, S>(
        param: &Self::LDTParameters,
        codewords_oracles: Vec<&mut SuccinctRoundOracleVarView<F>>,
        ldt_transcript: &mut SimulationTranscriptVar<F, MT, MTG, S>,
    ) -> Result<(), SynthesisError>
    where
        MT: Config,
        MTG: ConfigGadget<MT, F, Leaf = [FpVar<F>]>,
        S: SpongeWithGadget<F>,
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<F>,
    {
        let namespace = &ROOT_NAMESPACE;
        let num_oracles = codewords_oracles
            .iter()
            .map(|round| round.oracle.info.num_reed_solomon_codes_oracles())
            .sum::<usize>();
        ldt_transcript.squeeze_verifier_field_elements(num_oracles)?;
        ldt_transcript.submit_verifier_current_round(&ROOT_NAMESPACE, iop_trace!());

        let mut current_domain = param.fri_parameters.domain;

        // receive ldt message oracles
        // receive ldt message oracles
        param.fri_parameters.localization_parameters
            [0..param.fri_parameters.localization_parameters.len() - 1]
            .iter()
            .zip(param.fri_parameters.localization_parameters[1..].iter())
            .try_for_each(
                |(&localization_curr, &localization_next)| -> Result<_, SynthesisError> {
                    ldt_transcript.squeeze_verifier_field_elements(1)?;
                    ldt_transcript.submit_verifier_current_round(namespace, iop_trace!());

                    let next_domain = current_domain.fold(localization_curr);
                    ldt_transcript.receive_prover_current_round(
                        namespace,
                        ProverRoundMessageInfo {
                            reed_solomon_code_degree_bound: Vec::default(), // none
                            num_message_oracles: 1,
                            num_short_messages: 0,
                            localization_parameter: localization_next as usize,
                            oracle_length: next_domain.size(),
                        },
                        iop_trace!(),
                    )?;

                    current_domain = next_domain;
                    Ok(())
                },
            )?;

        // receive final polynomials

        ldt_transcript.squeeze_verifier_field_elements(1)?;
        ldt_transcript.submit_verifier_current_round(namespace, iop_trace!());
        ldt_transcript.receive_prover_current_round(
            namespace,
            ProverRoundMessageInfo {
                reed_solomon_code_degree_bound: Vec::default(),
                num_message_oracles: 0,
                num_short_messages: 1,
                localization_parameter: 0, // ignored
                oracle_length: 0,          // ignored
            },
            iop_trace!(),
        )?;

        Ok(())
    }

    fn query_and_decide_var<S: SpongeWithGadget<F>>(
        param: &Self::LDTParameters,
        random_oracle: &mut S::Var,
        mut codewords_oracles: Vec<&mut SuccinctRoundOracleVarView<F>>,
        mut ldt_prover_message_oracles: Vec<&mut SuccinctRoundOracleVarView<F>>,
        ldt_verifier_messages: &[Vec<VerifierMessageVar<F>>],
    ) -> Result<(), SynthesisError> {
        let codeword_log_num_cosets = param.fri_parameters.domain.dim()
            - param.fri_parameters.localization_parameters[0] as usize;

        let query_indices = (0..param.num_queries)
            .map(|_| random_oracle.squeeze_bits(codeword_log_num_cosets))
            .collect::<Result<Vec<_>, _>>()?;

        // restore random coefficients and alphas
        let random_coefficients = ldt_verifier_messages[0][0]
            .clone()
            .try_into_field_elements()
            .unwrap();

        let alphas = ldt_verifier_messages[1..]
            .iter()
            .map(|vm| {
                assert_eq!(vm.len(), 1);
                let vm_curr = vm[0].clone().try_into_field_elements().unwrap();
                assert_eq!(vm_curr.len(), 1);
                vm_curr.into_iter().next().unwrap()
            })
            .collect::<Vec<_>>();

        query_indices
            .into_iter()
            .try_for_each(|coset_index| -> Result<(), SynthesisError> {
                // prepare query
                let (query_cosets, query_indices, domain_final) =
                    FRIVerifierGadget::prepare_query(coset_index, &param.fri_parameters)?;

                // get query responses in codewords oracles
                let mut codewords_oracle_responses = (0..query_cosets[0].size())
                    .map(|_| FpVar::constant(F::zero()))
                    .collect::<Vec<_>>();

                codewords_oracles
                    .iter_mut()
                    .map(|oracle| {
                        let query_responses = oracle
                            .query_coset(
                                &[query_indices[0].clone()],
                                iop_trace!("rl_ldt query codewords"),
                            )
                            .pop()
                            .unwrap()
                            .into_iter()
                            .map(|round| round.into_iter());
                        let degrees = oracle.get_degree_bound();
                        query_responses.zip(degrees.into_iter())
                    })
                    .flatten()
                    .zip(random_coefficients.iter())
                    .try_for_each(
                        |((msg, degree_bound), coeff)| -> Result<(), SynthesisError> {
                            assert_eq!(codewords_oracle_responses.len(), msg.len());
                            assert!(param.fri_parameters.tested_degree > degree_bound as u64);
                            let degree_raise_poly_at_coset = degree_raise_poly_query(
                                param.fri_parameters.domain,
                                param.fri_parameters.tested_degree - degree_bound as u64,
                                param.fri_parameters.localization_parameters[0],
                                &query_indices[0],
                            )?;
                            debug_assert_eq!(
                                codewords_oracle_responses.len(),
                                degree_raise_poly_at_coset.len()
                            );
                            codewords_oracle_responses
                                .iter_mut()
                                .zip(msg.into_iter().zip(degree_raise_poly_at_coset.into_iter()))
                                .for_each(|(dst, (src_oracle, src_raise))| {
                                    *dst += coeff * &src_oracle * src_raise
                                });
                            Ok(())
                        },
                    )?;

                // get query responses in ldt prover messages oracles
                assert_eq!(ldt_prover_message_oracles.len(), query_indices.len());
                let round_oracle_responses = query_indices[1..]
                    .iter()
                    .zip(ldt_prover_message_oracles.iter_mut())
                    .map(|(query_index, msg)| {
                        let mut response = msg
                            .query_coset(
                                &[query_index.clone()],
                                iop_trace!("rl_ldt query fri message"),
                            )
                            .pop()
                            .unwrap();
                        assert_eq!(response.len(), 1);
                        response.pop().unwrap()
                    })
                    .collect::<Vec<_>>();

                // get final polynomial
                let final_polynomial_coeffs = ldt_prover_message_oracles
                    .last()
                    .unwrap()
                    .get_short_message(0)
                    .to_vec();
                let total_shrink_factor = param
                    .fri_parameters
                    .localization_parameters
                    .iter()
                    .sum::<u64>();
                let final_poly_degree_bound =
                    param.fri_parameters.tested_degree >> total_shrink_factor;

                assert!(final_polynomial_coeffs.len() <= (final_poly_degree_bound + 1) as usize); // we should let prover do `generate_low_degree_coefficients
                let final_polynomial =
                    DensePolynomialVar::from_coefficients_vec(final_polynomial_coeffs);
                let result = FRIVerifierGadget::consistency_check(
                    &param.fri_parameters,
                    &query_indices,
                    &query_cosets,
                    &ark_std::iter::once(codewords_oracle_responses)
                        .chain(round_oracle_responses.into_iter())
                        .collect::<Vec<_>>(),
                    &alphas,
                    &domain_final,
                    &final_polynomial,
                )?;

                result.enforce_equal(&Boolean::TRUE)
            })
    }
}

/// return evaluation of x^{degree_to_raise} at specific location (with coset structure)
/// For now, we assume the offset of codeword domain is constant.
/// TODO: in the future, the offset can also be an variable.
fn degree_raise_poly_query<F: PrimeField>(
    domain: Radix2CosetDomain<F>,
    degree_to_raise: u64,
    log_coset_size: u64,
    coset_index: &[Boolean<F>],
) -> Result<Vec<FpVar<F>>, SynthesisError> {
    let mut result = Vec::with_capacity(1 << log_coset_size);
    let dist_between_coset_elems = 1 << (domain.dim() - log_coset_size as usize);

    let mut curr = FpVar::constant(domain.offset.pow(&[degree_to_raise]))
        * FpVar::constant(domain.gen())
            .pow_le(coset_index)?
            .pow_by_constant(&[degree_to_raise])?;

    let step = FpVar::constant(
        domain
            .gen()
            .pow(&[dist_between_coset_elems])
            .pow(&[degree_to_raise]),
    );

    for _ in 0..(1 << log_coset_size) {
        result.push(curr.clone());
        curr *= &step;
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use crate::ldt::constraints::rl_ldt::degree_raise_poly_query;
    use ark_bls12_381::Fr;
    use ark_ldt::domain::Radix2CosetDomain;
    use ark_poly::polynomial::univariate::DensePolynomial;
    use ark_poly::UVPolynomial;
    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::boolean::Boolean;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::fields::FieldVar;
    use ark_r1cs_std::poly::domain::Radix2DomainVar;
    use ark_r1cs_std::poly::polynomial::univariate::dense::DensePolynomialVar;
    use ark_r1cs_std::R1CSVar;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::{One, Zero};

    #[test]
    fn test_degree_raise_poly() {
        let domain = Radix2CosetDomain::new_radix2_coset(64, Fr::from(123456u128));
        let domain_var = Radix2DomainVar {
            gen: domain.gen(),
            offset: FpVar::constant(domain.offset),
            dim: domain.dim() as u64,
        };
        let cs = ConstraintSystem::new_ref();
        // x^17
        let poly = DensePolynomial::from_coefficients_vec(
            (0..17)
                .map(|_| Fr::zero())
                .chain(ark_std::iter::once(Fr::one()))
                .collect(),
        );
        let poly_var = DensePolynomialVar::from_coefficients_vec(
            (0..17)
                .map(|_| FpVar::new_witness(cs.clone(), || Ok(Fr::zero())))
                .chain(ark_std::iter::once(FpVar::new_witness(cs.clone(), || {
                    Ok(Fr::one())
                })))
                .collect::<Result<Vec<_>, _>>()
                .unwrap(),
        );

        let expected_eval = domain.evaluate(&poly);

        let query_position = vec![Boolean::TRUE, Boolean::TRUE]; // 3

        let (queries, _) = domain.query_position_to_coset(3, 2);
        let expected_ans = queries
            .iter()
            .map(|&i| expected_eval[i])
            .collect::<Vec<_>>();

        let actual_ans = degree_raise_poly_query(domain, 17, 2, &query_position).unwrap();

        assert_eq!(expected_ans.len(), actual_ans.len());
        expected_ans
            .into_iter()
            .zip(actual_ans.into_iter())
            .for_each(|(expected, actual)| assert_eq!(expected, actual.value().unwrap()))
    }

    // ldt correctness is tested in mock protocol
}
