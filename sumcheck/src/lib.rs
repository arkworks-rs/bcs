use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_sponge::Absorb;

#[cfg(feature = "r1cs")]
pub mod constraints;
pub mod protocol;
#[cfg(test)]
pub(crate) mod test_util;
pub mod vp;

/// Univariate Sumcheck Protocol with a fixed summation domain
pub struct UnivariateSumcheck<F: PrimeField + Absorb> {
    pub summation_domain: Radix2CosetDomain<F>,
}
