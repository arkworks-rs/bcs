use crate::bcs::MTHashParameters;
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_crypto_primitives::MerkleTree;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
/// A trait for all oracle messages (including RS-code oracles, Non RS-code oracles, and IP short messages) sent in one round.
/// Those oracles (except IP short messages) need to have same length.
///
/// All oracle messages in the same prover round should will share one merkle tree. Each merkle tree leaf is
/// a vector which each element correspond to the same location of different oracles. The response of each query
/// is itself a vector where `result[i]` is oracle `i`'s leaf on this query position. All `reed_solomon_codes` oracle
/// will come first, and then message oracles.
pub trait RoundOracle<F: PrimeField>: Sized {
    /// Get short message in the oracle by index.
    fn get_short_message(&self, index: usize) -> &Vec<F>;

    /// Return the leaves of at `position` of all oracle. `result[i][j]` is leaf `i` at oracle `j`.
    fn query(&mut self, position: &[usize]) -> Vec<Vec<F>>;

    /// Return the leaves of at `position` of reed_solomon code oracle. `result[i][j]` is leaf `i` at oracle `j`.
    /// This method is convenient for LDT.
    /// Query position should be a coset, that has a starting index and stride.
    ///
    fn query_rs_code(&mut self, _starting_index: usize, _stride: usize) -> Vec<Vec<F>> {
        todo!("implement this once LDT is implemented")
        // two merkle trees: do we need to absorb the root of coset merkle tree as well?
    }

    /// Number of reed_solomon_codes oracles in this round.
    fn num_reed_solomon_codes_oracles(&self) -> usize;

    /// length of each oracle
    fn oracle_length(&self) -> usize;

    /// Get oracle info, including number of oracles for each type and degree bound of each RS code oracle.
    fn get_info(&self) -> ProverRoundMessageInfo;

    /// Get degree bound of all reed-solomon codes in this round.
    fn get_degree_bound(&self) -> Vec<usize> {
        self.get_info().reed_solomon_code_degree_bound
    }
}

#[derive(Clone)]
/// Contains all oracle messages in this round, and is storing queries, in order.
/// **Sponge absorb order**: Sponge will first absorb all merkle tree roots for `reed_solomon_codes`, then all merkle tree
/// roots for `message_oracles`, then all entire messages for `short_messages`.
pub struct RecordingRoundOracle<F: PrimeField> {
    /// Oracle evaluations with a degree bound.
    pub reed_solomon_codes: Vec<(Vec<F>, usize)>,
    /// Message oracles without a degree bound
    pub message_oracles: Vec<Vec<F>>,
    /// Messages without oracle sent in current round
    pub short_messages: Vec<Vec<F>>,
    /// length of each oracle message. `oracle_length` is 0 if in this round, prover sends only
    /// short messages.
    pub(crate) oracle_length: usize,
    /// Store the query position, in order
    pub queries: Vec<usize>,
    /// Contains information about leaf structure
    pub leaf_info: LeafStructure,
}

/// Stores whether the leaf of merkle tree contains a coset, or is individual leaf.
/// If the leaf is coset, the info also contains information about the stride of coset, and
/// each leaf will be a flattened 2d array where first axis is oracle index, and second axis is leaf positions.
///
/// For example, if the coset is `[3,6,9]` and we have 2 oracles, then the leaf will be
/// `[oracle[0][3], oracle[0][6], oracle[0][9], oracle[1][3], oracle[1][6], oracle[1][9]]`
///
/// TODO: implement coset as leaf
#[derive(Eq, PartialEq, Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LeafStructure {
    pub leaf_as_coset: bool,
    pub stride: usize,
}

impl Default for LeafStructure {
    fn default() -> Self {
        Self {
            leaf_as_coset: false,
            stride: 0,
        }
    }
}

/// Contains structure and degree bound information about prover round messages, but does not contain real messages.
#[derive(Eq, PartialEq, Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverRoundMessageInfo {
    pub reed_solomon_code_degree_bound: Vec<usize>,
    pub num_message_oracles: usize,
    pub num_short_messages: usize,
    pub oracle_length: usize,
    pub leaf_info: LeafStructure,
}

impl<F: PrimeField> Default for RecordingRoundOracle<F> {
    fn default() -> Self {
        RecordingRoundOracle {
            reed_solomon_codes: Vec::new(),
            message_oracles: Vec::new(),
            short_messages: Vec::new(),
            oracle_length: 0,
            queries: Vec::new(),
            leaf_info: LeafStructure::default(),
        }
    }
}

impl<F: PrimeField> RecordingRoundOracle<F> {
    pub fn set_leaf_structure(&mut self, _leaf_structure: &LeafStructure) {
        todo!()
    }

    /// Generate a merkle tree of `Self`.
    pub fn generate_merkle_tree<P: MTConfig<Leaf = [F]>>(
        &self, // all RS-codes, all message oracles
        hash_params: &MTHashParameters<P>,
        // todo (future): serialize by coset (stride) (element in same coset in same leaf): add addition
        // stride 3: [0: {oracle_1[0], oracle_2[0], ...},3,6,...], [1,4,7], ....
        // panic if stride is not divisible by oracle length
    ) -> Result<Option<MerkleTree<P>>, Error> {
        if self.oracle_length() == 0 {
            // oracle does not contain any message oracle
            debug_assert!(self.reed_solomon_codes.is_empty() && self.message_oracles.is_empty());
            return Ok(None);
        }
        if !self.oracle_length().is_power_of_two() {
            panic!("oracle length need to be power of two")
        }
        let all_positions: Vec<_> = (0..self.oracle_length).collect();
        let mt_leaves: Vec<_> = self.query_without_recording(&all_positions);

        Ok(Some(MerkleTree::<P>::new(
            &hash_params.leaf_hash_param,
            &hash_params.inner_hash_param,
            mt_leaves,
        )?))
    }

    pub fn get_succinct_oracle(&self) -> SuccinctRoundOracle<F> {
        let info = self.get_info();
        let leaves = self.query_without_recording(&self.queries);
        SuccinctRoundOracle {
            info,
            queried_leaves: leaves,
            short_messages: self.short_messages.clone(),
        }
    }

    fn query_without_recording(&self, position: &[usize]) -> Vec<Vec<F>> {
        let mut leaves: Vec<_> = (0..position.len()).map(|_| Vec::new()).collect();
        self.reed_solomon_codes
            .iter()
            .map(|msg| &msg.0)
            .chain(&self.message_oracles) // the oracles
            .for_each(|oracle| {
                if oracle.len() != self.oracle_length {
                    panic!("invalid oracle leaves");
                }

                for (i, pos) in position.into_iter().enumerate() {
                    leaves[i].push(oracle[*pos]);
                }
            });
        leaves
    }
}

impl<F: PrimeField> RoundOracle<F> for RecordingRoundOracle<F> {
    fn get_short_message(&self, index: usize) -> &Vec<F> {
        &self.short_messages[index]
    }

    fn query(&mut self, position: &[usize]) -> Vec<Vec<F>> {
        self.queries.extend_from_slice(position);
        self.query_without_recording(position)
    }

    fn num_reed_solomon_codes_oracles(&self) -> usize {
        self.reed_solomon_codes.len()
    }

    fn oracle_length(&self) -> usize {
        self.oracle_length
    }

    fn get_info(&self) -> ProverRoundMessageInfo {
        ProverRoundMessageInfo {
            reed_solomon_code_degree_bound: self
                .reed_solomon_codes
                .iter()
                .map(|(_, degree)| *degree)
                .collect(),
            num_message_oracles: self.message_oracles.len(),
            num_short_messages: self.short_messages.len(),
            oracle_length: self.oracle_length,
            leaf_info: self.leaf_info.clone(),
        }
    }
}

/// A round oracle that contains only leaves of queries.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SuccinctRoundOracle<F: PrimeField> {
    /// Oracle Info
    pub info: ProverRoundMessageInfo,
    /// Leaves at query indices.
    pub queried_leaves: Vec<Vec<F>>,
    // note that we do not store query position here, as they will be calculated in verifier
    /// Store the non-oracle IP messages in this round
    pub short_messages: Vec<Vec<F>>,
}

impl<F: PrimeField> SuccinctRoundOracle<F> {
    pub fn get_view(&self) -> SuccinctRoundOracleView<F> {
        SuccinctRoundOracleView {
            oracle: &self,
            queries: Vec::new(),
            current_query_pos: 0,
        }
    }
}

/// A reference to the oracle plus a state recording current query position.
#[derive(Clone)]
pub struct SuccinctRoundOracleView<'a, F: PrimeField> {
    pub(crate) oracle: &'a SuccinctRoundOracle<F>,
    /// Supposed queries of the verifier in order.
    pub queries: Vec<usize>,
    current_query_pos: usize,
}

impl<'a, F: PrimeField> RoundOracle<F> for SuccinctRoundOracleView<'a, F> {
    fn get_short_message(&self, index: usize) -> &Vec<F> {
        &self.oracle.short_messages[index]
    }

    fn query(&mut self, position: &[usize]) -> Vec<Vec<F>> {
        // maybe: type QueryEvaluations<F> = Vec<F>
        self.queries.extend_from_slice(position);
        assert!(
            self.current_query_pos + position.len() <= self.oracle.queried_leaves.len(),
            "too many queries"
        );
        let result = self.oracle.queried_leaves
            [self.current_query_pos..self.current_query_pos + position.len()]
            .to_vec();
        self.current_query_pos += position.len();
        result
    }

    fn num_reed_solomon_codes_oracles(&self) -> usize {
        self.oracle.info.reed_solomon_code_degree_bound.len()
    }

    fn oracle_length(&self) -> usize {
        self.oracle.info.oracle_length
    }

    fn get_info(&self) -> ProverRoundMessageInfo {
        self.oracle.info.clone()
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
