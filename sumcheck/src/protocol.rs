use crate::{
    vp::{DivVanishingPoly, VanishingPoly},
    UnivariateSumcheck,
};
use ark_bcs::iop::oracles::{CosetEvaluator, RecordingRoundOracle};
use ark_bcs::{
    bcs::transcript::{LDTInfo, Transcript},
    iop::{bookkeeper::NameSpace, message::CosetQueryResult, oracles::RoundOracle},
    iop_trace,
    prelude::{MessagesCollection, MsgRoundRef},
    IOPMTConfig,
};
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::{univariate::DensePolynomial, UVPolynomial};
use ark_sponge::{Absorb, CryptographicSponge};

#[derive(Debug, Clone, Copy)]
pub struct SumcheckPOracle<F: PrimeField + Absorb> {
    pub summation_domain: Radix2CosetDomain<F>,
    pub codeword_domain: Radix2CosetDomain<F>,

    pub claimed_sum: F,
    pub order_h_inv_times_claimed_sum: F,
}

impl<F: PrimeField + Absorb> SumcheckPOracle<F> {
    pub fn new(
        summation_domain: Radix2CosetDomain<F>,
        codeword_domain: Radix2CosetDomain<F>,
        claimed_sum: F,
    ) -> Self {
        let order_h_inv_times_claimed_sum =
            F::from(summation_domain.size() as u64).inverse().unwrap() * claimed_sum;
        Self {
            summation_domain,
            codeword_domain,
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
        // In the multiplicative case this is computing p in RS[L, (|H|-1) / L],
        //  where p as described in the paper is:
        //  p(x) = (|H| * f(x) - mu - |H| * Z_H(x) * h(x)) * (x^-1)
        //
        //  It is equivalent to check if the following is low degree:
        //  p'(x) = |H|^{-1}p(x)
        //        = (f(x) - |H|^{-1} * mu - Z_H(x) * h(x)) * (x^-1)
        //  We use the latter due to the reduced prover time.

        // axes: coset index, coset element index
        let h_eval = msgs
            .prover_round(h_oracle.0)
            .query_coset(coset_indices, iop_trace!("query h"))
            .at_oracle_index_owned(h_oracle.1);
        let f_eval = msgs
            .prover_round(f_oracle.0)
            .query_coset(coset_indices, iop_trace!("query f"))
            .at_oracle_index_owned(f_oracle.1);

        // TODO; split at here so that we have a function without `msgs`, so unit tesst can be easier
        let z_h = VanishingPoly::new(self.summation_domain);
        let z_h_eval = cosets.iter().map(|c| z_h.evaluation_over_coset(c));

        // for each coset:
        let result = f_eval
            .zip(h_eval)
            .zip(z_h_eval)
            .zip(cosets.iter())
            .map(|(((f, h), z_h_eval), coset)| {
                let mut curr_x_inv = coset.offset;
                let gen_inv = coset.gen().inverse().unwrap();
                f.into_iter()
                    .zip(h)
                    .zip(z_h_eval)
                    .map(|((f, h), z_h)| {
                        let result =
                            (f - self.order_h_inv_times_claimed_sum - z_h * h) * curr_x_inv;
                        curr_x_inv = curr_x_inv * gen_inv;
                        result
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<Vec<_>>>();
        CosetQueryResult::from_single_oracle_result(result)
    }

    /// Evaluate the low-degree virtual oracle on the whole codeword domain. This is useful for prover to run LDT because LDT need have access to the whole oracle.
    pub fn evaluate_whole_oracle(
        &self,
        h_eval: &[F],
        f_eval: &[F],
        z_h_eval: &[F],
        codeword_doamin: Radix2CosetDomain<F>,
    ) -> Vec<F> {
        let mut cur_x_inv = codeword_doamin.offset;
        let gen_inv = codeword_doamin.gen().inverse().unwrap();
        assert_eq!(h_eval.len(), f_eval.len());
        assert_eq!(h_eval.len(), z_h_eval.len());
        f_eval
            .iter()
            .zip(h_eval)
            .zip(z_h_eval)
            .map(|((f, h), z_h)| {
                let result = (*f - self.order_h_inv_times_claimed_sum - *z_h * *h) * cur_x_inv;
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
    /// # Panics
    /// Panics if there is a pending message not sent.
    pub fn send_sumcheck_prover_message<P: IOPMTConfig<F>, S: CryptographicSponge>(
        &self,
        transcript: &mut Transcript<P, S, F>,
        ns: NameSpace,
        f: &DensePolynomial<F>,
        f_in_transcript: (MsgRoundRef, usize),
        claimed_sum: F,
    ) where
        P::InnerDigest: Absorb,
    {
        let h = self.calculate_h(f);
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
            transcript.codeword_domain(),
            claimed_sum,
        );
        let g_vo = move |msg: &mut MessagesCollection<F, RecordingRoundOracle<F>>,
                         query: &[usize],
                         query_cosets: &[Radix2CosetDomain<F>]| {
            g_oracle.evaluate_oracle_query((h_handle, 0), f_in_transcript, msg, query, query_cosets)
        };
        let f_eval = &transcript
            .get_previously_sent_prover_round(f_in_transcript.0)
            .reed_solomon_codes()[f_in_transcript.1]
            .0;
        let z_h_eval = VanishingPoly::new(self.summation_domain)
            .evaluation_over_coset(&transcript.codeword_domain());
        let g_vo_whole = g_oracle.evaluate_whole_oracle(
            &h_eval,
            &f_eval,
            &z_h_eval,
            transcript.codeword_domain(),
        );

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
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::Field;
    use ark_ldt::domain::Radix2CosetDomain;
    use ark_poly::Polynomial;
    use ark_std::test_rng;

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
        let (h, g, actual_sum) = sumcheck.calculate_h_g_and_actual_sum(&f);

        let codeword_domain = Radix2CosetDomain::new_radix2_coset(128, Fr::from(256u64));
        // let expected_g_eval_over_h = codeword_domain
        //     .evaluate(&g)
        //     .iter()
        //     .map(|x| *x * Fr::from(summation_domain.size() as u64).inverse().unwrap()).collect::<Vec<_>>();

        let h_eval = codeword_domain.evaluate(&h);
        let f_eval = codeword_domain.evaluate(&f);
        let z_h_eval = VanishingPoly::new(summation_domain).evaluation_over_coset(&codeword_domain);

        let g_oracle = SumcheckPOracle::new(summation_domain, codeword_domain, actual_sum);
        let p = g_oracle.evaluate_whole_oracle(&h_eval, &f_eval, &z_h_eval, codeword_domain);

        let p_coeff = codeword_domain.interpolate(p);
        assert_eq!(p_coeff.degree(), summation_domain.size() - 2);
    }
}
