use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_std::borrow::Borrow;
use crate::iop::IOPVerifierMessage;
use ark_sponge::{CryptographicSponge, Absorb};
use crate::iop::transcript::Transcript;

/// A leaf-handling prover for public-coin IOP. This prover does not include low
/// degree test. Use RS-IOP Prover instead if the prover sends
/// polynomial using RS-code.
pub trait IOPProver<MT: MTConfig, S: CryptographicSponge>
where MT::InnerDigest: Absorb
{
    /// TODO doc
    type Leaf: Borrow<MT::Leaf>;
    /// TODO doc
    type VerifierMessage: IOPVerifierMessage<S>;

    /// TODO doc
    fn prove<T>(transcript: T)
        where T: Transcript<MT, S, Leaf = Self::Leaf, VerifierMessage = Self::VerifierMessage>;
}