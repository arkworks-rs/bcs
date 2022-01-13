use crate::{bcs::transcript::Transcript, iop::ProverParam};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

use super::bookkeeper::NameSpace;

/// A Prover for Public Coin IOP. This is intended to be used as an endpoint protocol. Any subprotocol does not need to implement this trait.
/// Any implementation of this trait can be transformed to SNARG by BCS.
pub trait IOPProver<F: PrimeField + Absorb> {
    /// Prover parameter should be a superset of verifier parameter.
    type ProverParameter: ProverParam;

    /// Public input
    type PublicInput: ?Sized;
    /// Private input
    type PrivateInput: ?Sized;

    /// Run the interactive prover, given the initial state, transcript, and
    /// parameter. If the prover involves a subprotocol, consider create a
    /// separate namespace for them.
    fn prove<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        namespace: NameSpace,
        public_input: &Self::PublicInput,
        private_input: &Self::PrivateInput,
        transcript: &mut Transcript<MT, S, F>,
        prover_parameter: &Self::ProverParameter,
    ) -> Result<(), crate::Error>
    where
        MT::InnerDigest: Absorb;
}
