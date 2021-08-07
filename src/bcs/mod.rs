use ark_crypto_primitives::merkle_tree::{Config as MTConfig, LeafParam, TwoToOneParam};

/// Defines a prover message oracle.
pub mod message;

/// TODO: refactor me!
pub mod prover;
/// TODO: refactor me!
pub mod transcript;
/// TODO: refactor me!
// pub mod verifier;

/// Specify the merkle tree hash parameters used for this protocol.
#[derive(Derivative)]
#[derivative(Clone(bound = "P: MTConfig"))]
pub struct MTHashParameters<P: MTConfig> {
    /// Leaf hash parameter of merkle tree.
    pub leaf_hash_param: LeafParam<P>,
    /// Inner hash (TwoToOneHash) parameter of merkle tree.
    pub inner_hash_param: TwoToOneParam<P>,
}
