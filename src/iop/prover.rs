use crate::bcs::transcript::{NameSpace, Transcript};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

/// A leaf-handling prover for public-coin IOP. This prover does not include low
/// degree test. Use RS-IOP Prover instead if the prover sends
/// polynomial using RS-code.
pub trait IOPProver<F: PrimeField + Absorb> {
    /// TODO doc
    type ProverParameter: ?Sized;
    /// Prover State
    type ProverState: ?Sized;
    /// maybe a prover state struct

    /// TODO doc
    ///
    /// If the prover involves a subprotocol, consider create a separate namespace for them,
    /// using `create_subprotocol_namespace(namespace)`. Doing so, subprotocol messages will not
    /// pollute the current namespace.
    fn prove<MT: MTConfig, S: CryptographicSponge>(
        state: &mut Self::ProverState,
        namespace: &NameSpace,
        transcript: &mut Transcript<MT, S, F>,
        prover_parameter: &Self::ProverParameter,
    ) where
        MT::InnerDigest: Absorb;
}
