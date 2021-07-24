use crate::bcs::transcript::{Transcript, NameSpace};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};
use crate::ldt_trait::LDT;

/// A leaf-handling prover for public-coin IOP. This prover does not include low
/// degree test. Use RS-IOP Prover instead if the prover sends
/// polynomial using RS-code.
pub trait IOPProver<MT: MTConfig, S: CryptographicSponge, F: PrimeField, L: LDT<MT, F>>
where
    MT::InnerDigest: Absorb,
{
    /// TODO doc
    type ProverParameter: ?Sized;
    /// Verifier Parameter (TODO: be included in prover parameter)
    type VerifierParameter: ?Sized;
    /// Prover State
    type ProverState: ?Sized;
    /// maybe a prover state struct

    /// TODO doc
    fn prove(
        state: &mut Self::ProverState,
        namespace: &NameSpace,
        transcript: Transcript<MT, S, F, L>,
        prover_parameter: &Self::ProverParameter,
        verifier_parameter: &Self::VerifierParameter,
    ) -> Transcript<MT, S, F, L>;
}
