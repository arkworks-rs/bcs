use crate::{
    vp::{DivVanishingPoly, VanishingPoly},
    UnivariateSumcheck,
};
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
    /// # Panics
    /// Panics if there is a pending message not sent.
    pub fn send_sumcheck_prover_message<P: IOPMTConfig<F>, S: CryptographicSponge>(
        &self,
        transcript: &mut Transcript<P, S, F>,
        ns: NameSpace,
        f: &DensePolynomial<F>,
    ) where
        P::InnerDigest: Absorb,
    {
        assert!(
            !transcript.is_pending_message_available(),
            "pending message not sent"
        );
        let h = self.calculate_h(f);
        // TODO: do we do LDT on h?
        let h_eval = transcript.codeword_domain().evaluate(&h);
        transcript.send_message_oracle(h_eval).unwrap();
        let h_oracle = transcript
            .submit_prover_current_round(ns, iop_trace!("h"))
            .unwrap();

        // register g as a virtual oracle
    }
}

pub struct SumcheckGOracle<F: PrimeField + Absorb> {
    pub summation_domain: Radix2CosetDomain<F>,
    pub codeword_domain: Radix2CosetDomain<F>,

    pub claimed_sum: F,
    pub order_h_inv_times_claimed_sum: F,
}

impl<F: PrimeField + Absorb> SumcheckGOracle<F> {
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

    pub fn evaluate_oracle<O: RoundOracle<F>>(
        &self,
        h_oracle: (MsgRoundRef, usize), // (round, oracle index): is oracle message (not LDTed)
        f_oracle: (MsgRoundRef, usize), // (round, oracle index)
        msgs: &mut MessagesCollection<F, O>,
        ns: NameSpace,
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

        let h_eval = msgs
            .prover_round(h_oracle.0)
            .query_coset(coset_indices, iop_trace!("query h"))
            .at_oracle_index_owned(h_oracle.1);
        let f_eval = msgs
            .prover_round(f_oracle.0)
            .query_coset(coset_indices, iop_trace!("query f"))
            .at_oracle_index_owned(f_oracle.1);

        let z_h = VanishingPoly::new(self.summation_domain);
        let z_h_eval = cosets.iter().map(|c| z_h.evaluation_over_coset(c));

        // point wise multiplication

        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
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
}
