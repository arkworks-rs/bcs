#![cfg_attr(not(feature = "std"), no_std)]
extern crate alloc;

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

impl<F: PrimeField + Absorb> UnivariateSumcheck<F> {
    pub fn new(summation_domain: Radix2CosetDomain<F>) -> Self {
        UnivariateSumcheck { summation_domain }
    }
}
