use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_sponge::Absorb;

pub mod vp;
pub mod protocol;

/// Univariate Sumcheck Protocol with a fixed summation domain
pub struct UnivariateSumcheck<F: PrimeField + Absorb>{
    pub summation_domain: Radix2CosetDomain<F>
}