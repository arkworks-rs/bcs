use ark_std::fmt::Debug;

/// Public Coin IOP Prover
pub mod prover;
/// Public coin IOP verifier
pub mod verifier;

/// Constraints for Public Coin IOP Verifier
#[cfg(feature = "r1cs")]
pub mod constraints;
/// Defines a prover message oracle.
pub mod message;
pub mod oracles;

/// A collection of oracle references from other protocols
/// used by current prover.
pub trait ProverOracleRefs: Clone + Debug {
    ///  A improper subset of `self` that will be used by verifier.
    type VerifierOracleRefs: VerifierOracleRefs;
    /// Derive Verifier state at the beginning of `query_and_decide` function
    /// using prover state at the end of commit phase.
    fn to_verifier_oracle_refs(&self) -> Self::VerifierOracleRefs;
}

impl ProverOracleRefs for () {
    type VerifierOracleRefs = ();

    fn to_verifier_oracle_refs(&self) -> Self::VerifierOracleRefs {
        ()
    }
}

/// A collection of oracle references from other protocols
/// used by current prover.
pub trait VerifierOracleRefs: Clone + Debug {}
impl<T: Clone + Debug> VerifierOracleRefs for T {}

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
