use ark_ff::PrimeField;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use ark_ldt::domain::Radix2CosetDomain;
use crate::bcs::message::{OracleWithCodewords, MessageOracle};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use crate::Error;

/// Trait for LDT.
/// TODO: move this into `ark-ldt`
pub trait LDT<MT: MTConfig, F: PrimeField> {

    type LDTProof: Clone + CanonicalSerialize + CanonicalDeserialize;
    type LDTParameters;

    /// Given the degree bound, reutnr the enforced bound and poly domain
    fn ldt_info(degree_bound: usize) -> (usize, Radix2CosetDomain<F>);

    fn prove<P: OracleWithCodewords<MT, F>>
    (param: Self::LDTParameters, codewords: &[&mut P]) -> Result<Self::LDTProof, Error>;

    fn verify<P: MessageOracle<MT, F>>
    (param: Self::LDTParameters, codewords: &[&mut P], proof: Self::LDTProof) -> Result<(), Error>;
}