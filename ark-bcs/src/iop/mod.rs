use ark_std::fmt::Debug;

/// Bookkeeping references to round oracles
pub mod bookkeeper;
/// Constraints for Public Coin IOP Verifier
#[cfg(feature = "r1cs")]
pub mod constraints;
/// Defines a prover message oracle.
pub mod message;
pub mod oracles;
/// Public Coin IOP Prover
pub mod prover;
/// Public coin IOP verifier
pub mod verifier;

/// Prover parameter used by IOP Prover.
pub trait ProverParam: Clone + Debug {
    /// Verifier state should be a improper subset of `self`.
    type VerifierParameter: VerifierParam;
    /// Derive Verifier state at the beginning of `query_and_decide` function
    /// using prover state at the end of commit phase.
    fn to_verifier_param(&self) -> Self::VerifierParameter;
}

impl ProverParam for () {
    type VerifierParameter = ();

    fn to_verifier_param(&self) -> Self::VerifierParameter {
        ()
    }
}

/// Parameter used by the IOP Verifier.
pub trait VerifierParam: Clone + Debug {}
impl<T: Clone + Debug> VerifierParam for T {}
