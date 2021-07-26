use crate::bcs::transcript::{NameSpace, Transcript};
use crate::ldt_trait::LDT;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

/// A leaf-handling prover for public-coin IOP. This prover does not include low
/// degree test. Use RS-IOP Prover instead if the prover sends
/// polynomial using RS-code.
pub trait IOPProver<MT: MTConfig, S: CryptographicSponge, F: PrimeField, L: LDT<MT, F, S>>
where
    MT::InnerDigest: Absorb,
{
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
    fn prove(
        state: &mut Self::ProverState,
        namespace: &NameSpace,
        transcript: Transcript<MT, S, F, L>,
        prover_parameter: &Self::ProverParameter,
    ) -> Transcript<MT, S, F, L>;
}
