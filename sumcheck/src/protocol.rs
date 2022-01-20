use crate::{
    vp::{DivVanishingPoly, VanishingPoly},
    UnivariateSumcheck,
};
use ark_bcs::iop::oracles::{RecordingRoundOracle, SuccinctRoundOracle};
use ark_bcs::prelude::{ProverRoundMessageInfo, SimulationTranscript};
use ark_bcs::{
    bcs::transcript::{LDTInfo, Transcript},
    iop::{bookkeeper::NameSpace, message::CosetQueryResult, oracles::RoundOracle},
    iop_trace,
    prelude::{MessagesCollection, MsgRoundRef},
};
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::{univariate::DensePolynomial, UVPolynomial};
use ark_sponge::{Absorb, CryptographicSponge};

#[derive(Debug, Clone, Copy)]
pub struct SumcheckPOracle<F: PrimeField + Absorb> {
    pub summation_domain: Radix2CosetDomain<F>,

    pub claimed_sum: F,
    pub order_h_inv_times_claimed_sum: F,
}

impl<F: PrimeField + Absorb> SumcheckPOracle<F> {
    pub fn new(
        summation_domain: Radix2CosetDomain<F>,
        claimed_sum: F,
    ) -> Self {
        let order_h_inv_times_claimed_sum =
            F::from(summation_domain.size() as u64).inverse().unwrap() * claimed_sum;
        Self {
            summation_domain,
            claimed_sum,
            order_h_inv_times_claimed_sum,
        }
    }

    /// evaluate the low-degree oracle, whose degree is `|H| - 2`
    pub fn evaluate_oracle_query<O: RoundOracle<F>>(
        &self,
        h_oracle: (MsgRoundRef, usize), // (round, oracle index): is oracle message (not LDTed)
        f_oracle: (MsgRoundRef, usize), // (round, oracle index)
        msgs: &mut MessagesCollection<F, O>,
        coset_indices: &[usize],
        cosets: &[Radix2CosetDomain<F>], // ret[i][j] is the j-th element of the i-th coset
    ) -> CosetQueryResult<F> {
        // axes: coset index, coset element index
        let h_eval = msgs
            .prover_round(h_oracle.0)
            .query_coset(coset_indices, iop_trace!("query h"))
            .at_oracle_index_owned(h_oracle.1);
        let f_eval = msgs
            .prover_round(f_oracle.0)
            .query_coset(coset_indices, iop_trace!("query f"))
            .at_oracle_index_owned(f_oracle.1);

        self.evaluate_oracle_query_inner(h_eval, f_eval, cosets)
    }

    pub fn evaluate_oracle_query_inner(
        &self,
        h_eval: impl IntoIterator<Item = Vec<F>>,
        f_eval: impl IntoIterator<Item = Vec<F>>,
        cosets: &[Radix2CosetDomain<F>],
    ) -> CosetQueryResult<F> {
        // In the multiplicative case this is computing p in RS[L, (|H|-1) / L],
        //  where p as described in the paper is:
        //  p(x) = (|H| * f(x) - mu - |H| * Z_H(x) * h(x)) * (x^-1)
        //
        //  It is equivalent to check if the following is low degree:
        //  p'(x) = |H|^{-1}p(x)
        //        = (f(x) - |H|^{-1} * mu - Z_H(x) * h(x)) * (x^-1)
        //  We use the latter due to the reduced prover time.

        // for each coset:
        let result = f_eval
            .into_iter()
            .zip(h_eval)
            .zip(cosets.iter())
            .map(|((f, h), coset)| self.evaluate_whole_oracle(&h, &f, *coset))
            .collect::<Vec<Vec<_>>>();
        CosetQueryResult::from_single_oracle_result(result)
    }

    /// Evaluate the low-degree virtual oracle on the whole codeword domain. This is useful for prover to run LDT because LDT need have access to the whole oracle.
    pub fn evaluate_whole_oracle(
        &self,
        h_eval: &[F],
        f_eval: &[F],
        coset_domain: Radix2CosetDomain<F>,
    ) -> Vec<F> {
        let mut cur_x_inv = coset_domain.offset.inverse().unwrap();
        let z_h_eval =
            VanishingPoly::new(self.summation_domain).evaluation_over_coset(&coset_domain);
        let gen_inv = coset_domain.gen().inverse().unwrap();
        assert_eq!(h_eval.len(), f_eval.len());
        assert_eq!(h_eval.len(), z_h_eval.len());
        assert_eq!(h_eval.len(), coset_domain.size());
        f_eval
            .iter()
            .zip(h_eval)
            .zip(z_h_eval)
            .map(|((f, h), z_h)| {
                let result = (*f - self.order_h_inv_times_claimed_sum - z_h * *h) * cur_x_inv;
                cur_x_inv = cur_x_inv * gen_inv;
                result
            })
            .collect::<Vec<_>>()
    }
}

impl<F: PrimeField + Absorb> UnivariateSumcheck<F> {
    /// Given a polynomial `f` to sum at domain `H`, return the actual sum, and
    /// polynomial `h` and `g` such that `p = h * Z_H + g * x + sum / |H|` where
    /// `Z_H` is the vanishing polynomial of `H`.
    ///
    /// # Returns
    /// * `h`: coefficient of polynomial `h` of degree `deg(f) - |H|`
    /// * `g`: coefficient of polynomial `g` of degree `|H| - 2`
    /// * `actual_sum`: actual sum of `f` over `H`
    pub fn calculate_h_g_and_actual_sum(
        &self,
        f: &DensePolynomial<F>,
    ) -> (DensePolynomial<F>, DensePolynomial<F>, F) {
        let vp = VanishingPoly::new(self.summation_domain);
        let (h, mut r) = f.divide_by_vp(vp);
        // we know r = x * g + sum / |H|. So g = (r - sum * |H|) / x
        let actual_sum = r.coeffs.remove(0) * F::from(self.summation_domain.size() as u64);
        let g = DensePolynomial::from_coefficients_vec(r.coeffs);
        (h, g, actual_sum)
    }

    pub fn degree_bound_of_g(&self) -> usize {
        self.summation_domain.size() - 1
    }

    /// Given a polynomial `f` to sum at domain `H`, return the actual sum, and
    /// polynomial `h` and `g` such that `p = h * Z_H + g * x + sum / |H|` where
    /// `Z_H` is the vanishing polynomial of `H`.
    ///
    /// # Returns
    /// * `h`: coefficient of polynomial `h`
    pub fn calculate_h(&self, f: &DensePolynomial<F>) -> DensePolynomial<F> {
        let vp = VanishingPoly::new(self.summation_domain);
        let (h, _) = f.divide_by_vp(vp);
        h
    }
    /// Send sumcheck message via transcript
    ///
    /// * `f`: coefficient of polynomial `f` to sum at domain `H`
    /// * `f_in_transcript`: where is `f` in transcript, represented as a round reference and an oracle index in that round
    /// * `is_f_bounded`: whether `f` has degree bound
    /// # Panics
    /// Panics if there is a pending message not sent.
    pub fn send_sumcheck_prover_message<P: Config<Leaf = [F]>, S: CryptographicSponge>(
        &self,
        transcript: &mut Transcript<P, S, F>,
        ns: NameSpace,
        f_coeff: &DensePolynomial<F>,
        f_in_transcript: (MsgRoundRef, usize),
        is_f_bounded: bool,
        claimed_sum: F,
    ) where
        P::InnerDigest: Absorb,
    {
        let h = self.calculate_h(f_coeff);
        // TODO: do we do LDT on h?
        let h_eval = transcript.codeword_domain().evaluate(&h);
        let h_handle = transcript
            .add_prover_round_with_codeword_domain()
            .send_oracle_message_without_degree_bound(h_eval.clone())
            .submit(ns, iop_trace!("h oracle"))
            .unwrap();

        // register g as a virtual oracle
        let g_oracle = SumcheckPOracle::new(
            self.summation_domain,
            claimed_sum,
        );
        let g_vo = move |msg: &mut MessagesCollection<F, RecordingRoundOracle<F>>,
                         query: &[usize],
                         query_cosets: &[Radix2CosetDomain<F>]| {
            g_oracle.evaluate_oracle_query((h_handle, 0), f_in_transcript, msg, query, query_cosets)
        };
        let f_eval = if is_f_bounded {
            &transcript
                .get_previously_sent_prover_round(f_in_transcript.0)
                .reed_solomon_codes()[f_in_transcript.1]
                .0
        } else {
            &transcript
                .get_previously_sent_prover_round(f_in_transcript.0)
                .message_oracles()[f_in_transcript.1]
        };
        let g_vo_whole =
            g_oracle.evaluate_whole_oracle(&h_eval, &f_eval, transcript.codeword_domain());

        let test_bound = self.degree_bound_of_g();
        transcript.register_prover_virtual_round(
            ns,
            Box::new(g_vo),
            vec![g_vo_whole],
            vec![test_bound],
            vec![test_bound],
            iop_trace!("g oracle"),
        );
    }

    /// Register sumcheck message via transcript
    pub fn register_sumcheck_commit_phase<P: Config<Leaf = [F]>, S: CryptographicSponge>(
        &self,
        transcript: &mut SimulationTranscript<P, S, F>,
        ns: NameSpace,
        f_in_transcript: (MsgRoundRef, usize),
        claimed_sum: F,
    ) where
        P::InnerDigest: Absorb,
    {
        // receive h with no degree bound
        let round_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
            .with_num_message_oracles(1)
            .build();
        let h_handle =
            transcript.receive_prover_current_round(ns, round_info, iop_trace!("h oracle"));

        // register g as a virtual oracle
        let g_oracle = SumcheckPOracle::new(
            self.summation_domain,
            claimed_sum,
        );
        let g_vo = move |msg: &mut MessagesCollection<F, SuccinctRoundOracle<F>>,
                         query: &[usize],
                         query_cosets: &[Radix2CosetDomain<F>]| {
            g_oracle.evaluate_oracle_query((h_handle, 0), f_in_transcript, msg, query, query_cosets)
        };
        let test_bound = self.degree_bound_of_g();
        transcript.register_prover_virtual_round(
            ns,
            Box::new(g_vo),
            vec![test_bound],
            vec![test_bound],
            iop_trace!("g oracle"),
        );
    }

    // there is no need to do query phase. LDT will fail is sum is incorrect.
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::poseidon_parameters;
    use ark_bcs::bcs::prover::BCSProof;
    use ark_bcs::bcs::MTHashParameters;
    use ark_bcs::iop::prover::IOPProver;
    use ark_bcs::iop::verifier::IOPVerifier;
    use ark_bcs::iop::ProverParam;
    use ark_bcs::ldt::rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters};
    use ark_bcs::Error;
    use ark_bls12_381::Fr;
    use ark_crypto_primitives::crh::poseidon;
    use ark_crypto_primitives::merkle_tree::{Config, IdentityDigestConverter};
    use ark_ldt::domain::Radix2CosetDomain;
    use ark_poly::Polynomial;
    use ark_sponge::poseidon::{PoseidonSponge};
    use ark_std::{test_rng, One};

    #[test]
    fn test_actual_sum() {
        let mut rng = test_rng();
        let summation_domain = Radix2CosetDomain::new_radix2_coset(64, Fr::from(123u64));
        let sumcheck = UnivariateSumcheck { summation_domain };
        let f = DensePolynomial::rand(100, &mut rng);
        let (h, g, actual_sum) = sumcheck.calculate_h_g_and_actual_sum(&f);
        let expected_sum = (0..summation_domain.size())
            .map(|i| f.evaluate(&summation_domain.element(i)))
            .sum::<Fr>();
        println!("degree of h: {}", h.degree());
        println!("degree of g: {}", g.degree());
        assert_eq!(actual_sum, expected_sum);
    }

    #[test]
    fn test_p_whole_oracle() {
        let mut rng = test_rng();
        let summation_domain = Radix2CosetDomain::new_radix2_coset(64, Fr::from(123u64));
        let f = DensePolynomial::rand(100, &mut rng);
        let sumcheck = UnivariateSumcheck { summation_domain };
        let (h, _, actual_sum) = sumcheck.calculate_h_g_and_actual_sum(&f);

        let codeword_domain = Radix2CosetDomain::new_radix2_coset(128, Fr::from(256u64));
        // let expected_g_eval_over_h = codeword_domain
        //     .evaluate(&g)
        //     .iter()
        //     .map(|x| *x * Fr::from(summation_domain.size() as u64).inverse().unwrap()).collect::<Vec<_>>();

        let h_eval = codeword_domain.evaluate(&h);
        let f_eval = codeword_domain.evaluate(&f);

        let g_oracle = SumcheckPOracle::new(summation_domain, actual_sum);
        let p = g_oracle.evaluate_whole_oracle(&h_eval, &f_eval, codeword_domain);

        let p_coeff = codeword_domain.interpolate(p);
        assert_eq!(p_coeff.degree(), summation_domain.size() - 2);

        // if claimed sum is wrong, the degree of `g` will be large.
        let wrong_g_oracle =
            SumcheckPOracle::new(summation_domain,  actual_sum + Fr::one());
        let p = wrong_g_oracle.evaluate_whole_oracle(&h_eval, &f_eval, codeword_domain);

        let p_coeff = codeword_domain.interpolate(p);
        assert!(p_coeff.degree() > summation_domain.size() - 2);
    }

    #[test]
    fn test_p_query_oracle() {
        let mut rng = test_rng();
        let summation_domain = Radix2CosetDomain::new_radix2_coset(64, Fr::from(123u64));
        let f = DensePolynomial::rand(100, &mut rng);
        let sumcheck = UnivariateSumcheck { summation_domain };
        let (h, _, actual_sum) = sumcheck.calculate_h_g_and_actual_sum(&f);

        let codeword_domain = Radix2CosetDomain::new_radix2_coset(128, Fr::from(256u64));

        let h_eval = codeword_domain.evaluate(&h);
        let f_eval = codeword_domain.evaluate(&f);

        let g_oracle = SumcheckPOracle::new(summation_domain,  actual_sum);
        let p = g_oracle.evaluate_whole_oracle(&h_eval, &f_eval, codeword_domain);

        let localization = 2usize;
        let num_cosets = codeword_domain.size() >> localization;
        let coset_indices = (0..num_cosets).collect::<Vec<_>>();
        let cosets = coset_indices
            .iter()
            .map(|i| codeword_domain.query_position_to_coset(*i, localization))
            .collect::<Vec<_>>();

        let h_eval_cosets = cosets
            .iter()
            .map(|(indices, _)| indices.iter().map(|i| h_eval[*i]).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let f_eval_cosets = cosets
            .iter()
            .map(|(indices, _)| indices.iter().map(|i| f_eval[*i]).collect::<Vec<_>>())
            .collect::<Vec<_>>();

        let actual_evals = g_oracle
            .evaluate_oracle_query_inner(
                h_eval_cosets,
                f_eval_cosets,
                &cosets.iter().map(|x| x.1).collect::<Vec<_>>(),
            )
            .assume_single_oracle();
        let expected_evals = cosets
            .iter()
            .map(|(pos, _)| pos.iter().map(|i| p[*i]).collect::<Vec<_>>())
            .collect::<Vec<_>>();

        assert_eq!(actual_evals.len(), expected_evals.len());
        assert_eq!(actual_evals, expected_evals);
    }

    pub struct MockProtocol;

    #[derive(Clone, Debug)]
    pub struct MockProverParam {
        pub poly: DensePolynomial<Fr>,
        pub claimed_sum: Fr,
        pub summation_domain: Radix2CosetDomain<Fr>,
    }

    #[derive(Clone, Debug)]
    pub struct MockVerifierParam {
        pub summation_domain: Radix2CosetDomain<Fr>,
        pub claimed_sum: Fr,
    }

    impl ProverParam for MockProverParam {
        type VerifierParameter = MockVerifierParam;

        fn to_verifier_param(&self) -> Self::VerifierParameter {
            MockVerifierParam {
                summation_domain: self.summation_domain.clone(),
                claimed_sum: self.claimed_sum.clone(),
            }
        }
    }

    impl IOPProver<Fr> for MockProtocol {
        type ProverParameter = MockProverParam;
        type PublicInput = ();
        type PrivateInput = ();

        fn prove<MT: Config<Leaf = [Fr]>, S: CryptographicSponge>(
            namespace: NameSpace,
            _public_input: &Self::PublicInput,
            _private_input: &Self::PrivateInput,
            transcript: &mut Transcript<MT, S, Fr>,
            prover_parameter: &Self::ProverParameter,
        ) -> Result<(), Error>
        where
            MT::InnerDigest: Absorb,
        {
            let poly_eval = transcript
                .codeword_domain()
                .evaluate(&prover_parameter.poly);
            let poly_handle = transcript
                .add_prover_round_with_codeword_domain()
                .send_oracle_message_without_degree_bound(poly_eval)
                .submit(namespace, iop_trace!("poly to sum"))?;
            // just invoke sumcheck
            let sumcheck = UnivariateSumcheck {
                summation_domain: prover_parameter.summation_domain,
            };
            let sumcheck_ns = transcript.new_namespace(namespace, iop_trace!("sumcheck"));
            sumcheck.send_sumcheck_prover_message(
                transcript,
                sumcheck_ns,
                &prover_parameter.poly,
                (poly_handle, 0),
                false,
                prover_parameter.claimed_sum,
            );
            Ok(())
        }
    }

    impl<S: CryptographicSponge> IOPVerifier<S, Fr> for MockProtocol {
        type VerifierOutput = ();
        type VerifierParameter = MockVerifierParam;
        type PublicInput = ();

        fn register_iop_structure<MT: Config<Leaf = [Fr]>>(
            namespace: NameSpace,
            transcript: &mut SimulationTranscript<MT, S, Fr>,
            verifier_parameter: &Self::VerifierParameter,
        ) where
            MT::InnerDigest: Absorb,
        {
            let poly_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
                .with_num_message_oracles(1)
                .build();
            let poly_handle = transcript.receive_prover_current_round(
                namespace,
                poly_info,
                iop_trace!("poly to sum"),
            );
            let sumcheck = UnivariateSumcheck {
                summation_domain: verifier_parameter.summation_domain,
            };
            let sumcheck_ns = transcript.new_namespace(namespace, iop_trace!("sumcheck"));
            sumcheck.register_sumcheck_commit_phase(
                transcript,
                sumcheck_ns,
                (poly_handle, 0),
                verifier_parameter.claimed_sum,
            );
        }

        fn query_and_decide<O: RoundOracle<Fr>>(
            _namespace: NameSpace,
            _verifier_parameter: &Self::VerifierParameter,
            _public_input: &Self::PublicInput,
            _sponge: &mut S,
            _transcript_messages: &mut MessagesCollection<Fr, O>,
        ) -> Result<Self::VerifierOutput, Error> {
            // nothing to do here. LDT is everything.
            Ok(())
        }
    }

    pub(crate) struct FieldMTConfig;

    pub(crate) type H = poseidon::CRH<Fr>;
    pub(crate) type TwoToOneH = poseidon::TwoToOneCRH<Fr>;

    impl Config for FieldMTConfig {
        type Leaf = [Fr];
        type LeafDigest = Fr;
        type LeafInnerDigestConverter = IdentityDigestConverter<Fr>;
        type InnerDigest = Fr;
        type LeafHash = H;
        type TwoToOneHash = TwoToOneH;
    }

    #[test]
    fn test_sumcheck_end_to_end() {
        let mut rng = test_rng();
        let sponge = PoseidonSponge::new(&poseidon_parameters());

        let codeword_domain = Radix2CosetDomain::new_radix2_coset(256, Fr::from(0x12345));
        let ldt_param = LinearCombinationLDTParameters::new(128, vec![1, 2, 1], codeword_domain, 5);
        let summation_domain = Radix2CosetDomain::new_radix2_coset(32, Fr::from(0x6789));

        let poly = DensePolynomial::rand(100, &mut rng);

        let claimed_sum = summation_domain.evaluate(&poly).into_iter().sum::<Fr>();

        let mt_hash_param = MTHashParameters::<FieldMTConfig> {
            leaf_hash_param: poseidon_parameters(),
            inner_hash_param: poseidon_parameters(),
        };

        let _ = BCSProof::generate::<MockProtocol, MockProtocol, LinearCombinationLDT<Fr>, _>(
            sponge,
            &(),
            &(),
            &MockProverParam {
                summation_domain,
                poly,
                claimed_sum,
            },
            &ldt_param,
            mt_hash_param,
        );

        // should not panic
    }
}
