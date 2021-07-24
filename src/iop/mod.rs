use ark_crypto_primitives::MerkleTree;
use ark_crypto_primitives::merkle_tree::{Config as MTConfig, LeafParam, TwoToOneParam};
use ark_ff::PrimeField;

use crate::Error;
use crate::bcs::message::MessageRecordingOracle;
use std::collections::BTreeMap;

/// Public Coin IOP Prover
pub mod prover;
/// TODO doc
pub mod verifier;

/// Subprotocol ID
pub type SubprotocolID = usize;

/// Specify the merkle tree hash parameters used for this protocol.
#[derive(Clone)]
pub struct MTHashParameters<P: MTConfig> {
    /// Leaf hash parameter of merkle tree.
    pub leaf_hash_param: LeafParam<P>,
    /// Inner hash (TwoToOneHash) parameter of merkle tree.
    pub inner_hash_param: TwoToOneParam<P>,
}

/// Prover message for leaf-handling IOP prover.
pub trait IOPProverMessage<P: MTConfig<Leaf = F>, F: PrimeField>: Sized {
    /// list of `Leaf`
    type OracleMessages: IntoIterator<Item = F>;
    /// Encode the prover message to merkle tree leaves.
    /// Make sure to pad the leaf size fo power of 2.
    fn to_oracle_messages(&self) -> Result<Self::OracleMessages, Error>;

    /// Encode the prover message to merkle tree.
    fn encode(&self, mt_param: &MTHashParameters<P>) -> Result<MessageRecordingOracle<P, F>, Error> {
        let leaves: Vec<_> = self.to_oracle_messages()?.into_iter().collect();
        let merkle_tree = MerkleTree::new(
            &mt_param.leaf_hash_param,
            &mt_param.inner_hash_param,
            leaves.clone(),
        )?;
        Ok(MessageRecordingOracle {
            leaves,
            merkle_tree,
            query_responses: BTreeMap::new()
        })
    }
}



