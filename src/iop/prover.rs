use crate::{
    bcs::transcript::{NameSpace, Transcript},
    iop::{ProverOracleRefs, ProverParam},
};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

/// A Prover for Public Coin IOP.
pub trait IOPProver<F: PrimeField + Absorb> {
    /// Prover parameter should be a superset of verifier parameter.
    type ProverParameter: ProverParam;

    /// A collection of oracle references from other protocols
    /// used by current prover.
    type RoundOracleRefs: ProverOracleRefs;

    /// Public input
    type PublicInput: ?Sized;
    /// Private input
    type PrivateInput: ?Sized;

    /// Run the interactive prover, given the initial state, transcript, and
    /// parameter. If the prover involves a subprotocol, consider create a
    /// separate namespace for them.
    fn prove<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        namespace: NameSpace,
        oracle_refs: &Self::RoundOracleRefs,
        public_input: &Self::PublicInput,
        private_input: &Self::PrivateInput,
        transcript: &mut Transcript<MT, S, F>,
        prover_parameter: &Self::ProverParameter,
    ) -> Result<(), crate::Error>
    where
        MT::InnerDigest: Absorb;
}

/// `IOPProverWithNoOracleRefs` is an auto-implemented trait. User does not need
/// to derive this trait manually.
///
/// This trait is an extension for IOPProver, which requires that the prover do
/// not need to have access to messages sent in other namespaces in the
/// same transcript. Most protocols that is not a subprotocol satisfy this
/// property.
///
/// Protocols that implements this trait can be used for BCS transform.
///
/// Any prover that `RoundOracleRefs = ()` will implement this trait
/// automatically.
pub trait IOPProverWithNoOracleRefs<F: PrimeField + Absorb>:
    IOPProver<F, RoundOracleRefs = ()>
{
}
impl<F: PrimeField + Absorb, Protocol: IOPProver<F, RoundOracleRefs = ()>>
    IOPProverWithNoOracleRefs<F> for Protocol
{
}
