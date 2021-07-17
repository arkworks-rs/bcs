use crate::iop::{EncodedProverMessage, ProverMessageOracle};
use crate::{BCSError, Error};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_crypto_primitives::Path;
use ark_std::borrow::Borrow;
use ark_std::collections::BTreeMap;

/// An oracle used when generating BCS proof. This oracle has access to
/// all bits, and will record all queries requested by verifier and responses.
pub struct MessageRecordingOracle<P: MTConfig, L: Borrow<P::Leaf> + Clone> {
    /// stores the prover message used for query
    pub encoded_message: EncodedProverMessage<P, L>,
    /// stores the responses
    pub query_responses: BTreeMap<usize, (L, Path<P>)>,
}

impl<P: MTConfig, L: Borrow<P::Leaf> + Clone> MessageRecordingOracle<P, L> {
    /// Convert `Self` to message fetching oracle, which will then be included in BCS Proof.
    pub fn into_message_fetching_oracle(self) -> MessageFetchingOracle<P, L> {
        MessageFetchingOracle {
            query_responses: self.query_responses,
        }
    }
}

impl<P: MTConfig, L: Borrow<P::Leaf> + Clone> ProverMessageOracle<P, L>
    for MessageRecordingOracle<P, L>
{
    fn query(&mut self, position: &[usize]) -> Result<Vec<(L, Path<P>)>, Error> {
        position
            .iter()
            .map(|&pos| {
                assert!(
                    pos < self.encoded_message.leaves.len(),
                    "requested position {} out of range",
                    pos
                );
                // record position
                let leaf = &self.encoded_message.leaves[pos];
                let proof = self.encoded_message.merkle_tree.generate_proof(pos)?;
                self.query_responses
                    .insert(pos, (leaf.clone(), proof.clone()));
                Ok((leaf.clone(), proof))
            })
            .collect()
    }
}

/// An oracle used when verifying BCS proof. This oracle only has access to queried bits.
pub struct MessageFetchingOracle<P: MTConfig, L: Borrow<P::Leaf> + Clone> {
    query_responses: BTreeMap<usize, (L, Path<P>)>,
}

impl<P: MTConfig, L: Borrow<P::Leaf> + Clone> ProverMessageOracle<P, L>
    for MessageFetchingOracle<P, L>
{
    fn query(&mut self, position: &[usize]) -> Result<Vec<(L, Path<P>)>, Error> {
        let mut result = Vec::with_capacity(position.len());
        for pos in position {
            match self.query_responses.get(pos) {
                Some((leaf, path)) => result.push((leaf.clone(), (*path).clone())),
                None => return Err(Box::new(BCSError::InvalidQuery)),
            }
        }
        Ok(result)
    }
}
