use crate::bcs::transcript::{NameSpace, Transcript};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

/// A leaf-handling prover for public-coin IOP. This prover does not include low
/// degree test. Use RS-IOP Prover instead if the prover sends
/// polynomial using RS-code.
pub trait IOPProver<F: PrimeField + Absorb> {
    /// TODO doc
    /// Prover parameter should be a superset of verifier parameter.
    type ProverParameter: ?Sized;

    /// Prover State. May contain witness.
    /// Prover state should be a superset of verifier state.
    type ProverState: ?Sized;
    /// Public input
    type PublicInput: ?Sized;

    /// TODO doc
    ///
    /// If the prover involves a subprotocol, consider create a separate namespace for them,
    /// using `create_subprotocol_namespace(namespace)`. Doing so, subprotocol messages will not
    /// pollute the current namespace.
    fn prove<MT: MTConfig, S: CryptographicSponge>(
        namespace: &NameSpace,
        state: &mut Self::ProverState,
        public_input: &Self::PublicInput,
        transcript: &mut Transcript<MT, S, F>,
        prover_parameter: &Self::ProverParameter,
    ) where
        MT::InnerDigest: Absorb;
}
