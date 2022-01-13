use ark_crypto_primitives::merkle_tree::{Config as MTConfig, LeafParam, TwoToOneParam};

/// BCS prover.
pub mod prover;
/// BCS transcript used by IOP Prover.
pub mod transcript;
/// BCS transcript used by IOP Verifier.
pub mod simulation_transcript;
/// BCS verifier.
pub mod verifier;

#[cfg(feature = "r1cs")]
/// R1CS Constraints for BCS.
pub mod constraints;
#[cfg(test)]
pub(crate) mod tests;

/// Specify the merkle tree hash parameters used for this protocol.
#[derive(Derivative)]
#[derivative(Clone(bound = "P: MTConfig"))]
pub struct MTHashParameters<P: MTConfig> {
    /// Leaf hash parameter of merkle tree.
    pub leaf_hash_param: LeafParam<P>,
    /// Inner hash (TwoToOneHash) parameter of merkle tree.
    pub inner_hash_param: TwoToOneParam<P>,
}
