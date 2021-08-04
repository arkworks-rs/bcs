use crate::bcs::MTHashParameters;
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_crypto_primitives::MerkleTree;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::collections::BTreeMap;
use ark_std::collections::BTreeSet;
use ark_std::iter::FromIterator;

/// A generalized RS-IOP message.
#[derive(Clone)]
/// `ProverMessagesInRound` contains all oracles sent in this round. Those oracles need to have
/// same length. Prover can also send short IP messages in this round, and those short messages do
/// not have length constraint.
///
/// All oracle messages in the same prover round should will share one merkle tree. Each merkle tree leaf is
/// a vector which each element correspond to the same location of different oracles.
///
/// **Sponge absorb order**: Sponge will first absorb all merkle tree roots for `reed_solomon_codes`, then all merkle tree
/// roots for `message_oracles`, then all entire messages for `short_messages`.
pub struct ProverMessagesInRound<F: PrimeField, Oracle: MessageOracle<F>> {
    /// Oracle evaluations with a degree bound.
    pub reed_solomon_codes: Vec<(Oracle, usize)>,
    /// Message oracles without a degree bound
    pub message_oracles: Vec<Oracle>,
    /// Messages without oracle sent in current round
    pub short_messages: Vec<Vec<F>>,
    /// length of each oracle message. `oracle_length` is 0 if in this round, prover sends only
    /// short messages.
    oracle_length: usize,
}

/// Contains structure and degree bound information about prover round messages, but does not contain real messages.
#[derive(Eq, PartialEq, Debug)]
pub struct ProverRoundMessageInfo {
    pub reed_solomon_code_degrees: Vec<usize>,
    pub num_message_oracles: usize,
    pub num_short_messages: usize,
    pub oracle_length: usize,
}

impl<F: PrimeField, Oracle: MessageOracle<F>> ProverMessagesInRound<F, Oracle> {
    pub fn empty() -> Self {
        ProverMessagesInRound {
            reed_solomon_codes: Vec::new(),
            message_oracles: Vec::new(),
            short_messages: Vec::new(),
            oracle_length: 0,
        }
    }
    pub fn oracle_length(&self) -> usize {
        self.oracle_length
    }
    pub fn get_info(&self) -> ProverRoundMessageInfo {
        ProverRoundMessageInfo {
            reed_solomon_code_degrees: self
                .reed_solomon_codes
                .iter()
                .map(|(_, degree)| *degree)
                .collect(),
            num_message_oracles: self.message_oracles.len(),
            num_short_messages: self.short_messages.len(),
            oracle_length: self.oracle_length,
        }
    }
}

impl<F: PrimeField, Oracle: OracleWithCodewords<F>> ProverMessagesInRound<F, Oracle> {
    /// Generate a merkle tree of `Self`.
    pub fn generate_merkle_tree<P: MTConfig<Leaf = Vec<F>>>(
        &self,
        hash_params: &MTHashParameters<P>,
    ) -> Result<Option<MerkleTree<P>>, Error> {
        if !self.oracle_length().is_power_of_two() {
            panic!("oracle length need to be power of two")
        }
        if self.oracle_length() == 0 {
            // oracle does not contain any message oracle
            debug_assert!(self.reed_solomon_codes.is_empty() && self.message_oracles.is_empty());
            return Ok(None);
        }
        let mut mt_leaves: Vec<_> = (0..self.oracle_length()).map(|_| Vec::new()).collect();
        let messages = self
            .reed_solomon_codes
            .iter()
            .map(|(oracle, _)| oracle)
            .chain(self.message_oracles.iter());
        for oracle in messages {
            if oracle.get_message().len() != self.oracle_length() {
                panic!("invalid oracle leaves");
            }
            mt_leaves
                .iter_mut()
                .zip(oracle.get_message().iter())
                .for_each(|(leaf, new)| {
                    leaf.push(*new);
                })
        }

        Ok(Some(MerkleTree::<P>::new(
            &hash_params.leaf_hash_param,
            &hash_params.inner_hash_param,
            mt_leaves,
        )?))
    }
}

impl<F: PrimeField> ProverMessagesInRound<F, MessageRecordingOracle<F>> {
    /// If `self` contains an oracle, remove all entries not queried to make. Return the union of query indices of
    /// all oracles, and the queried indices.
    pub fn into_succinct(self) -> (ProverMessagesInRound<F, SuccinctOracle<F>>, BTreeSet<usize>) {
        let mut query_indices = BTreeSet::new();
        for (oracle, _) in &self.reed_solomon_codes {
            query_indices = BTreeSet::from_iter(query_indices.union(&oracle.queries).map(|&x| x));
        }
        for oracle in &self.message_oracles {
            query_indices = BTreeSet::from_iter(query_indices.union(&oracle.queries).map(|&x| x));
        }

        let reed_solomon_codes = self
            .reed_solomon_codes
            .into_iter()
            .map(|(oracle, degree)| (oracle.get_succinct_oracle(&query_indices), degree))
            .collect();
        let message_oracles = self
            .message_oracles
            .into_iter()
            .map(|oracle| oracle.get_succinct_oracle(&query_indices))
            .collect();
        let short_messages = self.short_messages;
        let oracle_length = self.oracle_length;
        (
            ProverMessagesInRound {
                reed_solomon_codes,
                message_oracles,
                short_messages,
                oracle_length,
            },
            query_indices,
        )
    }
}

impl<F: PrimeField> ProverMessagesInRound<F, SuccinctOracle<F>>{
    /// Get a queryable prover messages.
    pub fn get_dummy_mut(&self) -> ProverMessagesInRound<F, &SuccinctOracle<F>> {
        ProverMessagesInRound{
            oracle_length: self.oracle_length,
            reed_solomon_codes: self.reed_solomon_codes.iter().map(|(a, b)|(a, *b)).collect(),
            short_messages: self.short_messages.clone(),
            message_oracles: self.message_oracles.iter().collect()
        }
    }
}

/// An Oracle of encoded message.
/// BCS prover will use this oracle to store queries and answers.
/// IOP Verifier will use this oracle to query prover message.
pub trait MessageOracle<F: PrimeField>: Clone {
    /// Query prover message at `position`. Returns answer and proof.
    ///
    /// `query` return error if oracle cannot fetch value at that position.
    ///
    /// Note that `query` does not do any merkle tree verification. Instead, in BCS verifier, merkle
    /// tree path check will be done separately.
    fn query(&mut self, position: &[usize]) -> Result<Vec<F>, Error>;
}

/// A message oracle, but with codewords that can be accessed by prover.
pub trait OracleWithCodewords<F: PrimeField>: MessageOracle<F> {
    /// Access the entire message without querying.
    fn get_message(&self) -> &[F];
}

/// An oracle used when generating BCS proof. This oracle contains the entire codeword.
#[derive(Clone)]
pub struct MessageRecordingOracle<F: PrimeField> {
    /// Prover message encoded to leaves.
    pub leaves: Vec<F>,
    /// Contain all the recorded queries.
    pub queries: BTreeSet<usize>,
}

impl<F: PrimeField> MessageRecordingOracle<F> {
    /// Convert `Self` to succinct oracle, which will then be included in BCS Proof.
    pub fn get_succinct_oracle(&self, queries: &BTreeSet<usize>) -> SuccinctOracle<F> {
        let query_responses_iter = queries
            .into_iter()
            .map(|query| (*query, *(self.leaves.get(*query).expect("invalid query"))));
        let query_responses = BTreeMap::from_iter(query_responses_iter);
        SuccinctOracle { query_responses }
    }
}

impl<F: PrimeField> MessageOracle<F> for MessageRecordingOracle<F> {
    fn query(&mut self, position: &[usize]) -> Result<Vec<F>, Error> {
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
                self.queries.insert(pos);
                Ok(*leaf)
            })
            .collect()
    }
}

impl<F: PrimeField> OracleWithCodewords<F> for MessageRecordingOracle<F> {
    fn get_message(&self) -> &[F] {
        &self.leaves
    }
}

/// An oracle that can be included in oracle proof.
/// This oracle only contains answers to queried bits.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SuccinctOracle<F: PrimeField> {
    query_responses: BTreeMap<usize, F>,
}

impl<F: PrimeField> SuccinctOracle<F> {
    pub(crate) fn available_indices(&self) -> Vec<usize> {
        self.query_responses.keys().map(|key|*key).collect()
    }
    
    pub(crate) fn query_no_mut(&self, position: &[usize]) -> Result<Vec<F>, Error> {
        let mut result = Vec::with_capacity(position.len());
        for pos in position {
            match self.query_responses.get(pos) {
                Some(leaf) => result.push(*leaf),
                None => panic!("oracle does not contain answer to this query"),
            }
        }
        Ok(result)
    }
}

impl<F: PrimeField> MessageOracle<F> for SuccinctOracle<F> {
    fn query(&mut self, position: &[usize]) -> Result<Vec<F>, Error> {
        self.query_no_mut(position)
    }
}

impl<F: PrimeField> MessageOracle<F> for &SuccinctOracle<F> {
    fn query(&mut self, position: &[usize]) -> Result<Vec<F>, Error> {
        self.query_no_mut(position)
    }
}

/// Verifier message used in transcript
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum VerifierMessage<F: PrimeField> {
    /// field elements
    FieldElements(Vec<F>),
    /// bits
    Bits(Vec<bool>),
    /// bytes
    Bytes(Vec<u8>),
}
