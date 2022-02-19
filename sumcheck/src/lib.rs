use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_sponge::Absorb;

pub mod vp;
pub mod protocol;
#[cfg(feature = "r1cs")]
pub mod constraints;
#[cfg(test)]
pub(crate) mod test_util;

/// Univariate Sumcheck Protocol with a fixed summation domain
pub struct UnivariateSumcheck<F: PrimeField + Absorb>{
    pub summation_domain: Radix2CosetDomain<F>
}