
use crate::{BCSError, Error};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_crypto_primitives::{Path, MerkleTree};
use ark_ff::PrimeField;
use ark_std::collections::BTreeMap;
use ark_std::marker::PhantomData;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize, Read, Write, SerializationError};

/// A generalized RS-IOP message.

#[derive(Derivative)]
#[derivative(Clone(bound="P: MTConfig, F: PrimeField, Oracle: MessageOracle<P, F>"))]
pub enum ProverMessage<P: MTConfig, F: PrimeField, Oracle: MessageOracle<P, F>>{
    /// Oracle evaluations
    ReedSolomonCode{degree_bound: usize, oracle: Oracle, _mt_config: PhantomData<P>},
    /// Message Oracle without degree bound
    MessageOracle{oracle: Oracle, _mt_config: PhantomData<P>},
    /// IP Message: Message without oracle
    IP{message: Vec<F>},
}

impl<P: MTConfig, F: PrimeField> ProverMessage<P, F, MessageRecordingOracle<P, F>>{
    /// If `self` contains an oracle, remove all entries not queried to make
    pub fn into_succinct(self) -> ProverMessage<P, F, SuccinctOracle<P, F>>{
        match self {
            ProverMessage::ReedSolomonCode {degree_bound, oracle,..} => ProverMessage::ReedSolomonCode {
                degree_bound, oracle: oracle.into_succinct_oracle(), _mt_config: PhantomData
            },
            ProverMessage::MessageOracle {oracle, ..} => ProverMessage::MessageOracle {
                oracle: oracle.into_succinct_oracle(), _mt_config: PhantomData
            },
            ProverMessage::IP{message} => ProverMessage::IP {message}
        }
    }
}

/// An Oracle of encoded message.
/// BCS prover will use this oracle to store queries and answers.
/// IOP Verifier will use this oracle to query prover message.
pub trait MessageOracle<P: MTConfig, F: PrimeField>: Clone {
    /// Query prover message at `position`. Returns answer and proof.
    ///
    /// `query` should return error if oracle cannot fetch value at that position.
    /// For example, in message oracle constructed from BCS proof, if query answer does not present
    /// in proof, this function will return an error.
    fn query(&mut self, position: &[usize]) -> Result<Vec<(F, Path<P>)>, Error>;

    /// Obtain the merkle tree root of the message.
    fn mt_root(&self) -> P::InnerDigest;
}

/// A message oracle, but with codewords
pub trait OracleWithCodewords<P: MTConfig, F: PrimeField>: MessageOracle<P, F> {
    /// Access the entire message without querying.
    fn get_message(&self) -> &[F];
}

/// An oracle used when generating BCS proof. This oracle contains the entire codeword.
#[derive(Derivative)]
#[derivative(Clone(bound = "P: MTConfig, F: PrimeField"))]
pub struct MessageRecordingOracle<P: MTConfig, F: PrimeField> {
    /// Prover message encoded to leaves.
    pub leaves: Vec<F>,
    /// Merkle tree for leaves. (change it to options)
    pub merkle_tree: MerkleTree<P>,
    /// Contains the query responses.
    pub query_responses: BTreeMap<usize, (F, Path<P>)>,
}

impl<P: MTConfig, F: PrimeField> MessageRecordingOracle<P, F> {
    /// Convert `Self` to message fetching oracle, which will then be included in BCS Proof.
    pub fn into_succinct_oracle(self) -> SuccinctOracle<P, F> {
        SuccinctOracle {
            query_responses: self.query_responses,
            mt_root: self.merkle_tree.root(),
        }
    }
}

impl<P: MTConfig, F: PrimeField> MessageOracle<P, F> for MessageRecordingOracle<P, F> {
    fn query(&mut self, position: &[usize]) -> Result<Vec<(F, Path<P>)>, Error> {
        position
            .iter()
            .map(|&pos| {
                assert!(
                    pos < self.leaves.len(),
                    "requested position {} out of range",
                    pos
                );
                // record position
                let leaf = &self.leaves[pos];
                let proof = self.merkle_tree.generate_proof(pos)?;
                self.query_responses
                    .insert(pos, (leaf.clone(), proof.clone()));
                Ok((leaf.clone(), proof))
            })
            .collect()
    }

    fn mt_root(&self) -> P::InnerDigest {
        self.merkle_tree.root()
    }
}

impl<P: MTConfig, F: PrimeField> OracleWithCodewords<P, F> for MessageRecordingOracle<P, F> {
    fn get_message(&self) -> &[F] {
        &self.leaves
    }
}

/// An oracle that can be included in oracle proof.
/// This oracle only contains answers to queried bits.
#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(Clone(bound = "P: MTConfig, F: PrimeField"))]
pub struct SuccinctOracle<P: MTConfig, F: PrimeField> {
    query_responses: BTreeMap<usize, (F, Path<P>)>,
    mt_root: P::InnerDigest,
}

impl<P: MTConfig, F: PrimeField> MessageOracle<P, F> for SuccinctOracle<P, F> {
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

/// Verifier message used in transcript
#[derive(Clone)]
pub enum VerifierMessage<F: PrimeField> {
    /// field elements
    FieldElements(Vec<F>),
    /// bits
    Bits(Vec<bool>),
    /// bytes
    Bytes(Vec<u8>)
}
