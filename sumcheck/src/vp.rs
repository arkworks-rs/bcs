use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::{univariate::DensePolynomial, Polynomial, UVPolynomial};
use ark_std::{ops::Mul, vec, vec::Vec, Zero};

/// Vanishing polynomial for a multiplicative coset H where |H| is a power of 2.
/// As H is a coset, every element can be described as b*g^i and therefore
/// has vanishing polynomial Z_H(x) = x^|H| - b^|H|
#[derive(Clone, Debug, Copy)]
pub struct VanishingPoly<F: PrimeField> {
    /// `|H|`: the size of the multiplicative coset
    degree: usize,
    /// `b^|H|`
    shift: F,
}

impl<F: PrimeField> VanishingPoly<F> {
    pub fn new(coset: Radix2CosetDomain<F>) -> Self {
        VanishingPoly {
            degree: coset.size(),
            shift: coset.offset.pow(&[coset.size() as u64]),
        }
    }

    /// point^|H| - b^|H|
    pub fn evaluation_at_point(&self, point: F) -> F {
        point.pow(&[self.degree as u64]) - self.shift
    }

    /// |H|*point^{|H| - 1}
    pub fn formal_derivative_at_point(&self, point: F) -> F {
        F::from(self.degree as u64) * point.pow(&[self.degree as u64 - 1])
    }

    /// Evaluate `self` (H) over `coset` (S). Returns `s ^ |H| - b^|H|` for all
    /// `s` in `S`. Reference: https://github.com/scipr-lab/libiop/blob/a2ed2ec2f3e85f29b6035951553b02cb737c817a/libiop/algebra/polynomials/vanishing_polynomial.tcc#L116
    pub fn evaluation_over_coset(&self, coset: &Radix2CosetDomain<F>) -> Vec<F> {
        // size of S
        let order_s = coset.size() as u64;
        // size of H
        let order_h = self.degree as u64;

        // Suppose S = hg^{i}, and the expected result is `h^|H| * g^{i|H|} - b^|H|`

        // h^|H|
        let shift_to_order_h = coset.offset.pow(&[order_h]);

        if order_h % order_s == 0 {
            // we know |S| <= |H| and |H| % |S| = 0.
            // so, g^{i|H|} = 1 for all i
            // so vp(s) = h^|H| - b^|H| for all s in S
            let vps = shift_to_order_h - self.shift;
            return vec![vps; coset.size()];
        }

        // g^|H|
        let coset_gen_to_order_h = coset.gen().pow(&[order_h]);

        if order_s % order_h == 0 {
            // we know |S| >= |H| and |S| % |H| = 0
            // therefore, f(X) = X^|H| is a homomorphism from S to a subgroup of order
            // |S|/|H| since P = X^|H| - shift, and shift is independent of X,
            // we can see there are only |S|/|H| distinct evaluations
            // and these repeat
            let num_distinct_eval = order_s / order_h;
            let evaluation_repetitions = order_h as usize;
            let mut cur = shift_to_order_h;
            (0..num_distinct_eval)
                .map(|_| {
                    let result = cur - self.shift;
                    cur *= coset_gen_to_order_h;
                    result
                })
                .collect::<Vec<_>>()
                .repeat(evaluation_repetitions)
        } else {
            let mut cur = shift_to_order_h;
            (0..order_s)
                .map(|_| {
                    let result = cur - self.shift;
                    cur *= coset_gen_to_order_h;
                    result
                })
                .collect()
        }
    }

    pub fn degree(&self) -> usize {
        self.degree
    }

    pub fn constant_coefficient(&self) -> F {
        self.shift
    }

    pub fn dense_poly(&self) -> DensePolynomial<F> {
        let mut coeffs = vec![F::zero(); self.degree + 1];
        coeffs[0] = -self.shift;
        coeffs[self.degree] = F::one();
        DensePolynomial::from_coefficients_vec(coeffs)
    }
}

impl<F: PrimeField> Mul<&DensePolynomial<F>> for VanishingPoly<F> {
    type Output = DensePolynomial<F>;

    fn mul(self, rhs: &DensePolynomial<F>) -> DensePolynomial<F> {
        // (x^|H| - b^|H|) * f(x) = x^|H| * f(x) - b^|H| * f(x)
        let mut result_coeffs = vec![F::zero(); rhs.degree() + self.degree + 1];

        // result += x^|H| * f(x)
        result_coeffs[self.degree..self.degree + rhs.coeffs.len()].copy_from_slice(&rhs.coeffs);
        result_coeffs[0..rhs.coeffs.len()]
            .iter_mut()
            .zip(rhs.coeffs.iter())
            .for_each(|(x, &a)| *x -= a * self.shift);
        DensePolynomial::from_coefficients_vec(result_coeffs)
    }
}

pub trait DivVanishingPoly<F: PrimeField>: Sized {
    /// divide `self` by `vp`. Return quotient and remainder.
    ///
    /// This function is different from `ark-poly::divide_by_vanishing_poly` in
    /// that this function supports vanishing polynomial for coset, which is
    /// more general.
    #[must_use]
    fn divide_by_vp(&self, vp: VanishingPoly<F>) -> (Self, Self);
}

impl<F: PrimeField> DivVanishingPoly<F> for DensePolynomial<F> {
    fn divide_by_vp(&self, vp: VanishingPoly<F>) -> (Self, Self) {
        // inverse of the leading term
        if self.degree() < vp.degree() {
            // `self` is remainder
            return (DensePolynomial::zero(), self.clone());
        }

        // suppose self = \sum_{i=0}^{k|H| + b} a_i x^i; vp = x^|H| - S
        // then, the quotient is \sum_{i=1}^{k|H| + b} a_i x^{i- |H|} + a_i * S * x^{i -
        // 2|H|} + a_i * S^2 * x^{i - 3|H|} + ...+ a_i * S^{k-1} * x^{i - k|H|}
        // where k is the maximum int such that i - k|H| >= 0
        let mut quotient_vec = self.coeffs[vp.degree..].to_vec();
        let mut s_pow = vp.shift;
        for r in 1..(self.len() / vp.degree) {
            // add a_i * S^{r + 1 -1} * x^{i - (r+1)|H|}
            quotient_vec
                .iter_mut()
                .zip(&self.coeffs[vp.degree * (r + 1)..])
                .for_each(|(s, &c)| *s += c * s_pow);
            s_pow *= vp.shift;
        }

        // remainder = self - quotient * vp
        // = self - quotient * (x^|H| - S)
        // = self.first_H_terms + self.other_terms - quotient * (x^|H| - S)
        // we know self.other_terms - quotient * x^|H| = 0 because remainder has degree
        // |H| so, remainder = self.first_H_terms - quotient * (-S) =
        // self.first_H_terms + quotient * s
        let mut remainder_vec = self.coeffs[..vp.degree].to_vec();
        remainder_vec
            .iter_mut()
            .zip(quotient_vec.iter())
            .for_each(|(a, &b)| *a += b * vp.shift);

        (
            DensePolynomial::from_coefficients_vec(quotient_vec),
            DensePolynomial::from_coefficients_vec(remainder_vec),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::Field;
    use ark_poly::{univariate::DenseOrSparsePolynomial, Polynomial};
    use ark_std::{test_rng, UniformRand};

    type F = ark_bls12_381::Fr;

    fn test_coset_evaluate_template(
        vp_coset: Radix2CosetDomain<F>,
        coset: Radix2CosetDomain<F>,
    ) -> Vec<F> {
        let expected_eval = (0..coset.size())
            .map(|i| {
                coset.element(i).pow(&[vp_coset.size() as u64])
                    - vp_coset.offset.pow(&[vp_coset.size() as u64])
            })
            .collect::<Vec<_>>();
        let actual_eval = VanishingPoly::new(vp_coset).evaluation_over_coset(&coset);
        assert_eq!(actual_eval, expected_eval);
        actual_eval
    }

    #[test]
    fn test_coset_template() {
        let mut rng = test_rng();
        let vp_domain = Radix2CosetDomain::new_radix2_coset(128, F::rand(&mut rng));
        // case 1: |S| <= |H| and |H| % |S| = 0.
        let coset = Radix2CosetDomain::new_radix2_coset(32, F::rand(&mut rng));
        test_coset_evaluate_template(vp_domain, coset);

        // case 1.2: |S| = |H|
        let coset = Radix2CosetDomain::new_radix2_coset(128, F::rand(&mut rng));
        test_coset_evaluate_template(vp_domain, coset);

        // case 2: |S| >= |H| and |S| % |H| = 0.
        let coset = Radix2CosetDomain::new_radix2_coset(256, F::rand(&mut rng));
        test_coset_evaluate_template(vp_domain, coset);

        // for now, it's not possible to have |S| % |H| != 0 or |H| % |S| != 0,
        // because they are both power of 2.

        // more complex case
        let coset = Radix2CosetDomain::new_radix2_coset(256, F::rand(&mut rng));
        let eval = test_coset_evaluate_template(vp_domain, coset);
        (0..(256usize >> 2)).for_each(|i| {
            let (pos, coset) = coset.query_position_to_coset(i, 2);
            let coset_eval = test_coset_evaluate_template(vp_domain, coset);
            let expected = pos.into_iter().map(|p| eval[p]).collect::<Vec<_>>();
            assert_eq!(coset_eval, expected);
        })
    }

    #[test]
    fn test_dense_poly() {
        let mut rng = test_rng();
        let vp_domain = Radix2CosetDomain::new_radix2_coset(256, F::rand(&mut rng));
        let vp = VanishingPoly::new(vp_domain);

        let point = F::rand(&mut rng);
        let expected = vp.evaluation_at_point(point);
        let actual = vp.dense_poly().evaluate(&point);
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_mul() {
        let mut rng = test_rng();
        let vp_domain = Radix2CosetDomain::new_radix2_coset(256, F::rand(&mut rng));
        let vp = VanishingPoly::new(vp_domain);

        let poly = DensePolynomial::<F>::rand(17, &mut rng);

        let point = F::rand(&mut rng);

        let expected = vp.evaluation_at_point(point) * poly.evaluate(&point);
        let actual = (vp * &poly).evaluate(&point);

        assert_eq!(actual, expected);
    }

    #[test]
    fn test_div() {
        let mut rng = test_rng();
        let vp_domain = Radix2CosetDomain::new_radix2_coset(128, F::rand(&mut rng));
        let vp = VanishingPoly::new(vp_domain);
        for d in 1..999 {
            let poly = DensePolynomial::rand(d, &mut rng);

            let (expected_q, expected_r) = DenseOrSparsePolynomial::from(poly.clone())
                .divide_with_q_and_r(&DenseOrSparsePolynomial::from(vp.dense_poly()))
                .unwrap();
            let (actual_q, actual_r) = poly.divide_by_vp(vp);

            assert_eq!(actual_q, expected_q);
            assert_eq!(actual_r, expected_r);
        }
    }
}
