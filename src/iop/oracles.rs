//! Code with message recording oracles and succinct oracles.
//! Verifier will not interact with those oracle directly. Instead, they will be
//! wrapped by MessageCollection.

use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;

use super::message::{MessagesCollection, ProverRoundMessageInfo};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
/// A trait for all oracle messages (including RS-code oracles, Non RS-code
/// oracles, and IP short messages) sent in one round. Those oracles (except IP
/// short messages) need to have same length.
///
/// All oracle messages in the same prover round should will share one merkle
/// tree. Each merkle tree leaf is a vector which each element correspond to the
/// same location of different oracles. The response of each query is itself a
/// vector where `result[i]` is oracle `i`'s leaf on this query position. All
/// `reed_solomon_codes` oracle will come first, and then message oracles.
pub trait RoundOracle<F: PrimeField>: Sized {
    /// Get short message in the oracle by index.
    fn get_short_message(&self, index: usize) -> &Vec<F>;

    /// Return the leaves of at `position` of all oracle. `result[i][j]` is leaf
    /// `i` at oracle `j`.
    #[tracing::instrument(skip(self))]
    fn query(&mut self, position: &[usize]) -> Vec<Vec<F>> {
        // convert the position to coset_index
        let log_coset_size = self.get_info().localization_parameter;
        let log_num_cosets = ark_std::log2(self.get_info().oracle_length) as usize - log_coset_size;
        let (coset_index, element_index_in_coset) =
            point_query_to_coset_query(position, log_num_cosets);

        let queried_coset = self.query_coset_without_tracer(&coset_index);

        coset_query_response_to_point_query_response(queried_coset, element_index_in_coset)
    }

    /// Return the queried coset at `coset_index` of all oracles.
    /// `result[i][j][k]` is coset index `i` -> oracle index `j` -> element `k`
    /// in this coset.
    #[tracing::instrument(skip(self))]
    fn query_coset(&mut self, coset_index: &[usize]) -> Vec<Vec<Vec<F>>> {
        self.query_coset_without_tracer(coset_index)
    }

    /// Return the queried coset at `coset_index` of all oracles, but without
    /// tracing information. `result[i][j][k]` is coset index `i` -> oracle
    /// index `j` -> element `k` in this coset.
    fn query_coset_without_tracer(&mut self, coset_index: &[usize]) -> Vec<Vec<Vec<F>>>;

    /// Number of reed_solomon_codes oracles in this round.
    fn num_reed_solomon_codes_oracles(&self) -> usize;

    /// length of each oracle
    fn oracle_length(&self) -> usize;

    /// Get oracle info, including number of oracles for each type and degree
    /// bound of each RS code oracle.
    fn get_info(&self) -> ProverRoundMessageInfo;

    /// Get degree bound of all reed-solomon codes in this round.
    fn get_degree_bound(&self) -> Vec<usize> {
        self.get_info().reed_solomon_code_degree_bound
    }
}

/// Given point indices, return coset index and element index in coset.
fn point_query_to_coset_query(
    point_indices: &[usize],
    log_num_cosets: usize,
) -> (Vec<usize>, Vec<usize>) {
    // coset index = position % num_cosets = the least significant `log_num_cosets`
    // bits of pos element index in coset = position / num_cosets = all
    // other bits
    let coset_index = point_indices
        .iter()
        .map(|&pos| pos & ((1 << log_num_cosets) - 1))
        .collect::<Vec<_>>();
    let element_index_in_coset = point_indices
        .iter()
        .map(|&pos| pos >> log_num_cosets)
        .collect::<Vec<_>>();
    (coset_index, element_index_in_coset)
}

/// Given queried coset elements, recovered the original point query responses.
fn coset_query_response_to_point_query_response<F: PrimeField>(
    queried_coset: Vec<Vec<Vec<F>>>,
    element_index_in_coset: Vec<usize>,
) -> Vec<Vec<F>> {
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

#[derive(Clone)]
/// Contains all oracle messages in this round, and is storing queries, in
/// order. **Sponge absorb order**: Sponge will first absorb all merkle tree
/// roots for `reed_solomon_codes`, then all merkle tree
/// roots for `message_oracles`, then all entire messages for `short_messages`.
pub struct RecordingRoundOracle<F: PrimeField> {
    /// Oracle Info
    pub info: ProverRoundMessageInfo,
    /// Store the queried coset index, in order
    pub queried_coset_index: Vec<usize>,
    /// All cosets. Axes: `[coset index, oracle index (RS-code first), element
    /// position in coset]`
    pub all_coset_elements: Vec<Vec<Vec<F>>>,
    /// low degree oracle evaluations in this round. The data stored is a
    /// duplicate to part of `all_coset_elements`, but is handy for prover wants
    /// to access it later.
    pub(crate) reed_solomon_codes: Vec<(Vec<F>, usize)>,
    /// message oracles with no degree bound in this round. The data stored is a
    /// duplicate to part of `all_coset_elements`, but is handy if the prover
    /// wants to access it later.
    pub(crate) message_oracles: Vec<Vec<F>>,
    /// Store the non-oracle IP messages in this round
    pub(crate) short_messages: Vec<Vec<F>>,
}

impl<F: PrimeField> RecordingRoundOracle<F> {
    /// Get reed solomon codes sent in this round.
    pub fn reed_solomon_codes(&self) -> &Vec<(Vec<F>, usize)> {
        &self.reed_solomon_codes
    }
    /// Get message oracles with degree bound sent in this round.
    pub fn message_oracles(&self) -> &Vec<Vec<F>> {
        &self.message_oracles
    }
    /// Get short non-oracle messages sent in this round.
    pub fn short_messages(&self) -> &Vec<Vec<F>> {
        &self.short_messages
    }

    /// Return a succinct oracle, which only contains queried responses.
    pub fn get_succinct(&self) -> SuccinctRoundMessage<F> {
        let info = self.get_info();
        let queried_cosets = self
            .queried_coset_index
            .iter()
            .map(|coset_index| self.all_coset_elements[*coset_index].clone())
            .collect::<Vec<_>>();
        SuccinctRoundMessage {
            info,
            queried_cosets,
            short_messages: self.short_messages.clone(),
        }
    }
}

impl<F: PrimeField> RoundOracle<F> for RecordingRoundOracle<F> {
    fn get_short_message(&self, index: usize) -> &Vec<F> {
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

/// Succinct Round message that is going to be included in the proof.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct SuccinctRoundMessage<F: PrimeField> {
    /// Oracle Info
    pub info: ProverRoundMessageInfo,
    /// Queried cosets. Axes `[query order, oracle index (RS-code first),
    /// element position in coset]`
    pub queried_cosets: Vec<Vec<Vec<F>>>,
    // note that we do not store query position here, as they will be calculated in verifier
    /// Store the non-oracle IP messages in this round
    pub short_messages: Vec<Vec<F>>,
}

impl<F: PrimeField> SuccinctRoundMessage<F> {
    /// Return a view of `self` such that the view records queries to the
    /// oracle.
    pub fn get_view(&self) -> SuccinctRoundOracle<F> {
        SuccinctRoundOracle {
            underlying_message: &self,
            coset_queries: Vec::new(),
            current_query_pos: 0,
        }
    }
}

/// A reference to the succinct round message plus a state recording current
/// query position.
#[derive(Clone)]
pub struct SuccinctRoundOracle<'a, F: PrimeField> {
    pub(crate) underlying_message: &'a SuccinctRoundMessage<F>,
    /// Supposed queries of the verifier in order.
    pub coset_queries: Vec<usize>,
    current_query_pos: usize,
}

impl<'a, F: PrimeField> RoundOracle<F> for SuccinctRoundOracle<'a, F> {
    fn get_short_message(&self, index: usize) -> &Vec<F> {
        &self.underlying_message.short_messages[index]
    }

    fn query_coset_without_tracer(&mut self, coset_index: &[usize]) -> Vec<Vec<Vec<F>>> {
        self.coset_queries.extend_from_slice(coset_index);
        assert!(
            self.current_query_pos + coset_index.len()
                <= self.underlying_message.queried_cosets.len(),
            "too many queries!"
        );
        let result = self.underlying_message.queried_cosets
            [self.current_query_pos..self.current_query_pos + coset_index.len()]
            .to_vec();
        self.current_query_pos += coset_index.len();
        result
    }

    fn num_reed_solomon_codes_oracles(&self) -> usize {
        self.underlying_message
            .info
            .reed_solomon_code_degree_bound
            .len()
    }

    fn oracle_length(&self) -> usize {
        self.underlying_message.info.oracle_length
    }

    fn get_info(&self) -> ProverRoundMessageInfo {
        self.underlying_message.info.clone()
    }
}

/// A coset evaluator defined by user, which takes a query position (as index
/// and coset) and use constituent oracles in iop messages to build up
/// responses.
pub type CosetEvaluator<F, O> = Box<
    dyn Fn(
            &mut MessagesCollection<F, O>, // iop_messages
            &[usize],                      // query_position as coset_index
            &[Radix2CosetDomain<F>],       // query cosets
        ) -> Vec<Vec<Vec<F>>>
        + 'static, /* result[i][j][k]` is coset index `i` -> oracle index `j`
                    * -> element `k`
                    * in this coset. */
>;

/// A virtual oracle who make query to other virtual or non-virtual oracles.
pub struct VirtualOracle<F: PrimeField, O: RoundOracle<F>> {
    coset_evaluator: CosetEvaluator<F, O>,
    pub(crate) codeword_domain: Radix2CosetDomain<F>,
    pub(crate) localization_param: usize,
    pub(crate) test_bound: Vec<usize>,
    #[allow(unused)]
    pub(crate) constraint_bound: Vec<usize>,
    // TODO: number of oracles
}

impl<F: PrimeField, O: RoundOracle<F>> VirtualOracle<F, O> {
    /// Create a new virtual round given a coset evaluator. Note that one
    /// virtual round can have multiple virtual oracles.
    pub fn new(
        coset_evaluator: CosetEvaluator<F, O>,
        codeword_domain: Radix2CosetDomain<F>,
        localization_param: usize,
        test_bound: Vec<usize>,
        constraint_bound: Vec<usize>,
    ) -> Self {
        Self {
            coset_evaluator,
            codeword_domain,
            localization_param,
            test_bound,
            constraint_bound,
        }
    }

    /// Query the virtual oracle points at `positions` in the codeword domain.
    pub fn query_point(
        &self,
        positions: &[usize],
        iop_messages: &mut MessagesCollection<F, O>,
    ) -> Vec<Vec<F>> {
        let log_coset_size = self.localization_param; // is also localization param
        let log_num_cosets = ark_std::log2(self.codeword_domain.size()) as usize - log_coset_size;

        let (coset_index, element_index_in_coset) =
            point_query_to_coset_query(positions, log_num_cosets);

        let queried_coset = self.query_coset(&coset_index, iop_messages);
        coset_query_response_to_point_query_response(queried_coset, element_index_in_coset)
    }

    /// Query the virtual oracle cosets at `coset_index` in the codeword domain.
    pub fn query_coset(
        &self,
        coset_index: &[usize],
        iop_messages: &mut MessagesCollection<F, O>,
    ) -> Vec<Vec<Vec<F>>> {
        // convert coset index to cosets
        let queried_cosets = coset_index
            .iter()
            .map(|&i| {
                self.codeword_domain
                    .query_position_to_coset(i, self.localization_param)
                    .1
            })
            .collect::<Vec<_>>();

        (self.coset_evaluator)(iop_messages, coset_index, &queried_cosets)
    }

    /// Get information about this oracle.
    pub fn get_info(&self) -> ProverRoundMessageInfo {
        ProverRoundMessageInfo::new(
            self.test_bound.clone(),
            0,
            0,
            self.codeword_domain.size(),
            self.localization_param,
        )
    }
}
