use crate::iop::{EncodedProverMessage, ProverMessageOracle};
use crate::{BCSError, Error};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_crypto_primitives::Path;
use ark_ff::PrimeField;
use ark_std::collections::BTreeMap;

/// An oracle used when generating BCS proof. This oracle has access to
/// all bits, and will record all queries requested by verifier and responses.
pub struct MessageRecordingOracle<P: MTConfig, F: PrimeField> {
    /// stores the prover message used for query
    pub encoded_message: EncodedProverMessage<P, F>,
    /// stores the responses
    pub query_responses: BTreeMap<usize, (F, Path<P>)>,
}

impl<P: MTConfig, F: PrimeField> MessageRecordingOracle<P, F> {
    /// Convert `Self` to message fetching oracle, which will then be included in BCS Proof.
    pub fn into_message_fetching_oracle(self) -> MessageFetchingOracle<P, F> {
        MessageFetchingOracle {
            query_responses: self.query_responses,
            mt_root: self.encoded_message.merkle_tree.root(),
        }
    }
}

impl<P: MTConfig, F: PrimeField> ProverMessageOracle<P, F> for MessageRecordingOracle<P, F> {
    fn query(&mut self, position: &[usize]) -> Result<Vec<(F, Path<P>)>, Error> {
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

    fn mt_root(&self) -> P::InnerDigest {
        self.encoded_message.merkle_tree.root()
    }
}

/// An oracle used when verifying BCS proof. This oracle only has access to queried bits.
pub struct MessageFetchingOracle<P: MTConfig, F: PrimeField> {
    query_responses: BTreeMap<usize, (F, Path<P>)>,
    mt_root: P::InnerDigest,
}

impl<P: MTConfig, F: PrimeField> ProverMessageOracle<P, F> for MessageFetchingOracle<P, F> {
    fn query(&mut self, position: &[usize]) -> Result<Vec<(F, Path<P>)>, Error> {
        let mut result = Vec::with_capacity(position.len());
        for pos in position {
            match self.query_responses.get(pos) {
                Some((leaf, path)) => result.push((leaf.clone(), (*path).clone())),
                None => return Err(Box::new(BCSError::InvalidQuery)),
            }
        }
        Ok(result)
    }

    fn mt_root(&self) -> P::InnerDigest {
        self.mt_root.clone()
    }
}
