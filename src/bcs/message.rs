use crate::bcs::MTHashParameters;
use crate::tracer::TraceInfo;
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_crypto_primitives::MerkleTree;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::vec::Vec;

/// A trait for all oracle messages (including RS-code oracles, Non RS-code oracles, and IP short messages) sent in one round.
/// Those oracles (except IP short messages) need to have same length.
///
/// All oracle messages in the same prover round should will share one merkle tree. Each merkle tree leaf is
/// a vector which each element correspond to the same location of different oracles. The response of each query
/// is itself a vector where `result[i]` is oracle `i`'s leaf on this query position. All `reed_solomon_codes` oracle
/// will come first, and then message oracles.
pub trait RoundOracle<F: PrimeField>: Sized {
    /// shows the name of implementation of oracle
    const TYPE: &'static str;

    /// Get short message in the oracle by index.
    fn get_short_message(&self, index: usize, tracer: TraceInfo) -> &Vec<F>;

    /// Return the leaves of at `position` of all oracle. `result[i][j]` is leaf `i` at oracle `j`.
    fn query(&mut self, position: &[usize], _tracer: TraceInfo) -> Vec<Vec<F>> {
        #[cfg(feature = "print-trace")]
        {
            println!(
                "[{}] Query {} leaves: {}",
                Self::TYPE,
                position.len(),
                _tracer
            )
        }
        // convert the position to coset_index
        let log_coset_size = self.get_info().localization_parameter;
        let log_num_cosets = ark_std::log2(self.get_info().oracle_length) as usize - log_coset_size;
        // coset index = position % num_cosets = the least significant `log_num_cosets` bits of pos
        // element index in coset = position / num_cosets = all other bits
        let coset_index = position
            .iter()
            .map(|&pos| pos & ((1 << log_num_cosets) - 1))
            .collect::<Vec<_>>();
        let element_index_in_coset = position
            .iter()
            .map(|&pos| pos >> log_num_cosets)
            .collect::<Vec<_>>();

        let queried_coset = self.query_coset_without_tracer(&coset_index);

        queried_coset
            .into_iter()
            .zip(element_index_in_coset.into_iter())
            .map(|(coset_for_all_oracles, element_index)| {
                coset_for_all_oracles
                    .into_iter()
                    .map(|coset| coset[element_index])
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    /// Return the queried coset at `coset_index` of all oracles.
    /// `result[i][j][k]` is coset index `i` -> oracle index `j` -> element `k` in this coset.
    fn query_coset(&mut self, coset_index: &[usize], _tracer: TraceInfo) -> Vec<Vec<Vec<F>>> {
        #[cfg(feature = "print-trace")]
        {
            println!(
                "[{}] Query {} cosets: {}",
                Self::TYPE,
                coset_index.len(),
                _tracer
            )
        }
        self.query_coset_without_tracer(coset_index)
    }

    /// Return the queried coset at `coset_index` of all oracles, but without tracing information. 
    /// `result[i][j][k]` is coset index `i` -> oracle index `j` -> element `k` in this coset.
    fn query_coset_without_tracer(&mut self, coset_index: &[usize]) -> Vec<Vec<Vec<F>>>;

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

pub(crate) struct PendingProverMessage<F: PrimeField> {
    /// Oracle evaluations with a degree bound.
    pub(crate) reed_solomon_codes: Vec<(Vec<F>, usize)>,
    /// Message oracles without a degree bound
    pub(crate) message_oracles: Vec<Vec<F>>,
    /// Messages without oracle sent in current round
    pub(crate) short_messages: Vec<Vec<F>>,
    /// length of each oracle message. `oracle_length` is 0 if in this round, prover sends only
    /// short messages.
    pub(crate) oracle_length: usize,
    /// localization parameter is log2(coset_size)
    /// Set it to zero to disable leaf as coset.
    pub(crate) localization_parameter: usize,
}

impl<F: PrimeField> Default for PendingProverMessage<F> {
    fn default() -> Self {
        Self {
            reed_solomon_codes: Vec::new(),
            message_oracles: Vec::new(),
            short_messages: Vec::new(),
            oracle_length: 0,
            localization_parameter: 0,
        }
    }
}

impl<F: PrimeField> PendingProverMessage<F> {
    fn has_oracle(&self) -> bool {
        self.oracle_length != 0
    }

    /// Generate a merkle tree of `Self` where each leaf is a coset.
    /// For example, if the coset is `[3,6,9]` and we have 2 oracles, then the leaf will be
    /// `[oracle[0][3], oracle[0][6], oracle[0][9], oracle[1][3], oracle[1][6], oracle[1][9]]`
    pub(crate) fn into_merkle_tree_and_recording_oracle<P: MTConfig<Leaf = [F]>>(
        self, // all RS-codes, all message oracles
        hash_params: &MTHashParameters<P>,
    ) -> Result<(Option<MerkleTree<P>>, RecordingRoundOracle<F>), Error> {
        let all_coset_elements = self.generate_all_cosets();
        let flattened_leaves = all_coset_elements
            .iter()
            .map(|oracles| oracles.iter().flatten().map(|x| *x).collect::<Vec<_>>());
        let mt = if self.has_oracle() {
            Some(MerkleTree::new(
                &hash_params.leaf_hash_param,
                &hash_params.inner_hash_param,
                flattened_leaves,
            )?)
        } else {
            None
        };
        let info = ProverRoundMessageInfo {
            oracle_length: self.oracle_length,
            reed_solomon_code_degree_bound: self
                .reed_solomon_codes
                .iter()
                .map(|(_, degree)| *degree)
                .collect(),
            localization_parameter: self.localization_parameter,
            num_short_messages: self.short_messages.len(),
            num_message_oracles: self.message_oracles.len(),
        };
        let recording_oracle = RecordingRoundOracle {
            info,
            reed_solomon_codes: self.reed_solomon_codes,
            short_messages: self.short_messages,
            all_coset_elements,
            queried_coset_index: Vec::new(),
        };
        Ok((mt, recording_oracle))
    }

    /// Generate a un-flattened merkle tree leaves
    ///
    /// result axes:`[coset index, oracle index, element index in coset]`
    pub(crate) fn generate_all_cosets(&self) -> Vec<Vec<Vec<F>>> {
        if !self.has_oracle() {
            return Vec::new();
        }
        let coset_size = 1 << self.localization_parameter;
        debug_assert_eq!(self.oracle_length % coset_size, 0);
        let num_cosets = self.oracle_length / coset_size;
        let stride = num_cosets;
        // axes: [coset index, oracle index, element index in coset]
        // absolute position = coset index + stride * element_index
        (0..num_cosets)
            .map(|coset_index| {
                self.reed_solomon_codes
                    .iter()
                    .map(|(oracle, _)| oracle)
                    .chain(self.message_oracles.iter())
                    .map(|oracle| {
                        (0..coset_size)
                            .map(|element_index| oracle[coset_index + stride * element_index])
                            .collect::<Vec<_>>()
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    }
}

#[derive(Clone)]
/// Contains all oracle messages in this round, and is storing queries, in order.
/// **Sponge absorb order**: Sponge will first absorb all merkle tree roots for `reed_solomon_codes`, then all merkle tree
/// roots for `message_oracles`, then all entire messages for `short_messages`.
pub struct RecordingRoundOracle<F: PrimeField> {
    /// Oracle Info
    pub info: ProverRoundMessageInfo,
    /// Store the queried coset index, in order
    pub queried_coset_index: Vec<usize>,
    /// All cosets. Axes: `[coset index, oracle index (RS-code first), element position in coset]`
    pub all_coset_elements: Vec<Vec<Vec<F>>>,
    /// low degree oracle evaluations in this round. The data stored is a duplicate to part of `all_coset_elements`, but is handy for LDT to process.
    pub reed_solomon_codes: Vec<(Vec<F>, usize)>,
    /// Store the non-oracle IP messages in this round
    pub short_messages: Vec<Vec<F>>,
}

/// If the leaf is coset, the info also contains information about the stride of coset, and
/// each leaf will be a flattened 2d array where first axis is oracle index, and second axis is leaf positions.
///
/// For example, if the coset is `[3,6,9]` and we have 2 oracles, then the leaf will be
/// `[oracle[0][3], oracle[0][6], oracle[0][9], oracle[1][3], oracle[1][6], oracle[1][9]]`

/// Contains structure and degree bound information about prover round messages, but does not contain real messages.
#[derive(Eq, PartialEq, Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverRoundMessageInfo {
    /// Degree bounds of oracle evaluations, in order.
    pub reed_solomon_code_degree_bound: Vec<usize>,
    /// Number of message oracles without degree bound. Those oracles will not be processed by LDT.
    pub num_message_oracles: usize,
    /// Number of short messages. Those messages will be included in proof in entirety.
    pub num_short_messages: usize,
    /// Length of each message oracles in current round.
    pub oracle_length: usize,
    /// log2(coset size)
    /// Set it to zero to disable leaf as coset.
    pub localization_parameter: usize,
}

impl ProverRoundMessageInfo {
    /// Number of message oracles with degree bound.
    pub fn num_reed_solomon_codes_oracles(&self) -> usize {
        self.reed_solomon_code_degree_bound.len()
    }

    /// Number of oracles, including those with or without degree bound.
    pub fn num_oracles(&self) -> usize {
        self.num_reed_solomon_codes_oracles() + self.num_message_oracles
    }
}

impl<F: PrimeField> RecordingRoundOracle<F> {
    /// Return a succinct oracle, which only contains queried responses.
    pub fn get_succinct_oracle(&self) -> SuccinctRoundOracle<F> {
        let info = self.get_info();
        let queried_cosets = self
            .queried_coset_index
            .iter()
            .map(|coset_index| self.all_coset_elements[*coset_index].clone())
            .collect::<Vec<_>>();
        SuccinctRoundOracle {
            info,
            queried_cosets,
            short_messages: self.short_messages.clone(),
        }
    }
}

impl<F: PrimeField> RoundOracle<F> for RecordingRoundOracle<F> {
    const TYPE: &'static str = "Recording Round Oracle";

    fn get_short_message(&self, index: usize, _tracer: TraceInfo) -> &Vec<F> {
        #[cfg(feature = "print-trace")]
        {
            println!(
                "[Recording oracle] Get short message at index {}: {}",
                index, _tracer
            )
        }
        &self.short_messages[index]
    }

    fn query_coset_without_tracer(&mut self, coset_index: &[usize]) -> Vec<Vec<Vec<F>>> {
        // record the coset query
        self.queried_coset_index.extend_from_slice(coset_index);
        let result = coset_index
            .iter()
            .map(|coset_index| {
                self.all_coset_elements[*coset_index % self.all_coset_elements.len()].clone()
            })
            .collect::<Vec<_>>();
        result
    }

    fn num_reed_solomon_codes_oracles(&self) -> usize {
        self.info.num_reed_solomon_codes_oracles()
    }

    fn oracle_length(&self) -> usize {
        self.info.oracle_length
    }

    fn get_info(&self) -> ProverRoundMessageInfo {
        self.info.clone()
    }
}

/// A round oracle that contains only leaves of queries.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SuccinctRoundOracle<F: PrimeField> {
    /// Oracle Info
    pub info: ProverRoundMessageInfo,
    /// Queried cosets. Axes `[query order, oracle index (RS-code first), element position in coset]`
    pub queried_cosets: Vec<Vec<Vec<F>>>,
    // note that we do not store query position here, as they will be calculated in verifier
    /// Store the non-oracle IP messages in this round
    pub short_messages: Vec<Vec<F>>,
}

impl<F: PrimeField> SuccinctRoundOracle<F> {
    /// Return a view of `self` such that the view records queries to the oracle.
    pub fn get_view(&self) -> SuccinctRoundOracleView<F> {
        SuccinctRoundOracleView {
            oracle: &self,
            coset_queries: Vec::new(),
            current_query_pos: 0,
        }
    }
}

/// A reference to the oracle plus a state recording current query position.
#[derive(Clone)]
pub struct SuccinctRoundOracleView<'a, F: PrimeField> {
    pub(crate) oracle: &'a SuccinctRoundOracle<F>,
    /// Supposed queries of the verifier in order.
    pub coset_queries: Vec<usize>,
    current_query_pos: usize,
}

impl<'a, F: PrimeField> RoundOracle<F> for SuccinctRoundOracleView<'a, F> {
    const TYPE: &'static str = "Succinct Round Oracle View";

    fn get_short_message(&self, index: usize, _tracer: TraceInfo) -> &Vec<F> {
        #[cfg(feature = "print-trace")]
        {
            println!(
                "[Succinct Round oracle] Get short message at index {}: {}",
                index, _tracer
            )
        }
        &self.oracle.short_messages[index]
    }

    fn query_coset_without_tracer(&mut self, coset_index: &[usize]) -> Vec<Vec<Vec<F>>> {
        self.coset_queries.extend_from_slice(coset_index);
        assert!(
            self.current_query_pos + coset_index.len() <= self.oracle.queried_cosets.len(),
            "too many queries!"
        );
        let result = self.oracle.queried_cosets
            [self.current_query_pos..self.current_query_pos + coset_index.len()]
            .to_vec();
        self.current_query_pos += coset_index.len();
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

impl<F: PrimeField> VerifierMessage<F> {
    /// If `self` contains field elements, return those elements. Otherwise return `None`.
    pub fn try_into_field_elements(self) -> Option<Vec<F>> {
        if let Self::FieldElements(x) = self {
            Some(x)
        } else {
            None
        }
    }

    /// If `self` contains bits, return those bits. Otherwise return `None`.
    pub fn try_into_bits(self) -> Option<Vec<bool>> {
        if let Self::Bits(x) = self {
            Some(x)
        } else {
            None
        }
    }

    /// If `self` contains bytes, return those bytes. Otherwise return `None`.
    pub fn try_into_bytes(self) -> Option<Vec<u8>> {
        if let Self::Bytes(x) = self {
            Some(x)
        } else {
            None
        }
    }
}
