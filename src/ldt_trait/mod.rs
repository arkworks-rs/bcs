use crate::bcs::message::{MessageOracle, OracleWithCodewords};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_sponge::CryptographicSponge;

/// Trait for LDT.
/// TODO: move this into `ark-ldt`
pub trait LDT<MT: MTConfig, F: PrimeField, S: CryptographicSponge> {
    type LDTProof: Clone + CanonicalSerialize + CanonicalDeserialize;
    type LDTParameters;

    /// Given the degree bound, reutnr the enforced bound and poly domain
    fn ldt_info(degree_bound: usize) -> (usize, Radix2CosetDomain<F>);

    /// Given the list of codewords along with its degree bound, generate the LDT proof.
    /// The LDT proof will not include the codeword oracle, but verifier will need to access the
    /// oracle afterwords.
    ///
    /// **important**: when simulating verifier in LDT, make sure verifier can only access prover message
    /// though `oracle.query`.  
    fn prove<P: OracleWithCodewords<MT, F>>(
        param: &Self::LDTParameters,
        sponge: &mut S,
        codewords: &[(usize, &mut P)],
    ) -> Result<Self::LDTProof, Error>;

    fn verify<P: MessageOracle<MT, F>>(
        param: &Self::LDTParameters,
        sponge: &mut S,
        codewords: &[&mut P],
        proof: Self::LDTProof,
    ) -> Result<(), Error>;
}
