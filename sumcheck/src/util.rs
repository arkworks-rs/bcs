use crate::UnivariateSumcheck;
use ark_ff::PrimeField;
use ark_poly::univariate::DensePolynomial;
use ark_poly::UVPolynomial;
use crate::vp::{DivVanishingPoly, VanishingPoly};

impl<F: PrimeField> UnivariateSumcheck<F> {
    /// Given a polynomial `f` to sum at domain `H`, return the actual sum, and
    /// polynomial `h` and `g` such that `p = h * Z_H + g * x + sum` where `Z_H` is the
    /// vanishing polynomial of `H`.
    ///
    /// # Returns
    /// * `h`: coefficient of polynomial `h`
    /// * `g`: coefficient of polynomial `g`
    /// * `actual_sum`: actual sum of `f` over `H`
    pub fn calculate_h_g_and_actual_sum(
        &self,
        f: &DensePolynomial<F>,
    ) -> (DensePolynomial<F>, DensePolynomial<F>, F) {
        let vp = VanishingPoly::new(self.summation_domain);
        let (h, mut r) = f.divide_by_vp(vp);
        // we know r = x * g + sum. So g = (r - sum) / x // TODO: PR on https://github.com/scipr-lab/libiop/blob/master/libiop/protocols/encoded/sumcheck/sumcheck.tcc#L378
        let actual_sum = r.coeffs.remove(0) * F::from(self.summation_domain.size() as u64);
        let g = DensePolynomial::from_coefficients_vec(r.coeffs);
        (h, g, actual_sum)
    }
}

#[cfg(test)]
mod tests{
    use ark_bls12_381::Fr;
    use ark_ldt::domain::Radix2CosetDomain;
    use ark_poly::Polynomial;
    use ark_std::test_rng;
    use super::*;

    #[test]
    fn test_h_g(){
        let mut rng = test_rng();
        let summation_domain = Radix2CosetDomain::new_radix2_coset(64, Fr::from(123u64));
        let sumcheck = UnivariateSumcheck{summation_domain};
        let f = DensePolynomial::rand(100, &mut rng);
        let (h, g, actual_sum) = sumcheck.calculate_h_g_and_actual_sum(&f);
        let expected_sum = (0..summation_domain.size()).map(|i| {
            f.evaluate(&summation_domain.element(i))
        }).sum::<Fr>();
        println!("degree of h: {}", h.degree());
        println!("degree of g: {}", g.degree());
        assert_eq!(actual_sum, expected_sum);
    }
}
