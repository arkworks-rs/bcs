use crate::bcs::Transcript;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

/// A leaf-handling prover for public-coin IOP. This prover does not include low
/// degree test. Use RS-IOP Prover instead if the prover sends
/// polynomial using RS-code.
pub trait IOPProver<MT: MTConfig, S: CryptographicSponge, F: PrimeField>
where
    MT::InnerDigest: Absorb,
{
    /// TODO doc
    type ProverParameter: ?Sized;
    /// Verifier Parameter
    type VerifierParameter: ?Sized;

    /// TODO doc
    fn prove(
        transcript: Transcript<MT, S, F>,
        prover_parameter: &Self::ProverParameter,
        verifier_parameter: &Self::VerifierParameter,
    ) -> Transcript<MT, S, F>;
}
