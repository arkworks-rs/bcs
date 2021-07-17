use crate::iop::transcript::Transcript;
use crate::iop::IOPVerifierMessage;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::borrow::Borrow;

/// A leaf-handling prover for public-coin IOP. This prover does not include low
/// degree test. Use RS-IOP Prover instead if the prover sends
/// polynomial using RS-code.
pub trait IOPProver<MT: MTConfig, S: CryptographicSponge>
where
    MT::InnerDigest: Absorb,
{
    /// TODO doc
    type ProverParameter: ?Sized;
    /// TODO doc
    type Leaf: Borrow<MT::Leaf> + Clone;
    /// TODO doc
    type VerifierMessage: IOPVerifierMessage<S>;

    /// TODO doc
    fn prove<T, Parameter: Borrow<Self::ProverParameter>>(
        transcript: &mut T,
        prover_parameter: Parameter,
    ) where
        T: Transcript<MT, S, Leaf = Self::Leaf, VerifierMessage = Self::VerifierMessage>;
}
