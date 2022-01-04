use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;

pub mod vp;
pub mod util;

/// Univariate Sumcheck Protocol with a fixed summation domain
pub struct UnivariateSumcheck<F: PrimeField>{
    pub summation_domain: Radix2CosetDomain<F>
}