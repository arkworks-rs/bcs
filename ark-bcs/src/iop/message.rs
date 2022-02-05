use crate::prelude::SimulationTranscript;
use crate::{iop::bookkeeper::MessageBookkeeper, tracer::TraceInfo};
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::vec::Vec;
use std::iter::FromIterator;

use crate::iop::message::LeavesType::{Custom, UseCodewordDomain};
use tracing::info;

use super::{
    bookkeeper::{BookkeeperContainer, ToMsgRoundRef},
    oracles::{RoundOracle, VirtualOracleWithInfo},
};

/// Contains location of round oracles in a transcript.
#[derive(Clone, Copy, Debug)]
pub struct MsgRoundRef {
    pub(crate) index: usize,
    pub(crate) trace: TraceInfo,
    /// Whether this round refers to an virtual oracle.
    pub(crate) is_virtual: bool,
}

impl MsgRoundRef {
    /// Returns a new `RoundOracleRef
    pub fn new(index: usize, trace: TraceInfo, is_virtual: bool) -> Self {
        MsgRoundRef {
            index,
            trace,
            is_virtual,
        }
    }

    /// Get the trace for the round oracle reference.
    pub fn trace(&self) -> TraceInfo {
        self.trace
    }
}

/// Stores sent prover and verifier messages in order.
/// Message can be accessed using namespace, or `MsgRoundRef`.
/// This struct is used by verifier to access prover message oracles and
/// verifier messages.
pub struct MessagesCollection<F: PrimeField, O: RoundOracle<F>> {
    pub(crate) real_oracles: Vec<O>,
    pub(crate) virtual_oracles: Vec<Option<VirtualOracleWithInfo<F, O>>>,
    pub(crate) verifier_messages: Vec<Vec<VerifierMessage<F>>>,
    pub(crate) bookkeeper: MessageBookkeeper,
}

impl<F: PrimeField, O: RoundOracle<F>> MessagesCollection<F, O> {
    pub(crate) fn new(
        real_oracles: Vec<O>,
        virtual_oracles: Vec<Option<VirtualOracleWithInfo<F, O>>>,
        verifier_messages: Vec<Vec<VerifierMessage<F>>>,
        bookkeeper: MessageBookkeeper,
    ) -> Self {
        Self {
            real_oracles,
            virtual_oracles,
            verifier_messages,
            bookkeeper,
        }
    }

    /// Given a `MsgRoundRef`, return the corresponding verifier message.
    pub fn verifier_round(&self, at: impl ToMsgRoundRef) -> &Vec<VerifierMessage<F>> {
        let at = at.to_verifier_msg_round_ref(&self.bookkeeper);
        &self.verifier_messages[at.index]
    }

    /// Given a `MsgRoundRef`, return the corresponding prover round message.
    pub fn prover_round(&mut self, at: impl ToMsgRoundRef) -> AtProverRound<F, O> {
        let round = at.to_prover_msg_round_ref(&self.bookkeeper);
        AtProverRound { _self: self, round }
    }

    /// Get metadata of current prover round message.
    pub fn get_prover_round_info(&self, at: impl ToMsgRoundRef) -> ProverRoundMessageInfo {
        let at = at.to_prover_msg_round_ref(&self.bookkeeper);
        if at.is_virtual {
            self.virtual_oracles
                .get(at.index)
                .expect("round out of range")
                .as_ref()
                .expect("Virtual oracle contains circular query: For example, A -> B -> C -> A")
                .get_info()
        } else {
            self.real_oracles[at.index].get_info()
        }
    }

    /// Take a virtual oracle and return a shadow `self` that can be used by
    /// virtual oracle. Current `self` will be temporarily unavailable when
    /// querying to prevent circular dependency.
    fn take_virtual_oracle(&mut self, round: MsgRoundRef) -> (VirtualOracleWithInfo<F, O>, Self) {
        assert!(round.is_virtual);

        // move a virtual oracle, and make it temporarily available when querying to
        // prevent circular dependency
        let virtual_round = ark_std::mem::take(
            self.virtual_oracles
                .get_mut(round.index)
                .expect("round out of range"),
        )
        .expect("Virtual oracle contains circular query: For example, A -> B -> C -> A");

        // construct a shadow MessageCollection to query the virtual oracle.
        let shadow_self = Self {
            bookkeeper: self.bookkeeper.clone(),
            real_oracles: ark_std::mem::take(&mut self.real_oracles),
            virtual_oracles: ark_std::mem::take(&mut self.virtual_oracles),
            verifier_messages: ark_std::mem::take(&mut self.verifier_messages),
        };

        (virtual_round, shadow_self)
    }

    fn restore_from_shadow_self(
        &mut self,
        shadow_self: Self,
        round: MsgRoundRef,
        vo: VirtualOracleWithInfo<F, O>,
    ) {
        self.real_oracles = shadow_self.real_oracles;
        self.virtual_oracles = shadow_self.virtual_oracles;
        self.verifier_messages = shadow_self.verifier_messages;
        self.virtual_oracles[round.index] = Some(vo);
    }
}

impl<F: PrimeField, O: RoundOracle<F>> BookkeeperContainer for MessagesCollection<F, O> {
    fn _bookkeeper(&self) -> &MessageBookkeeper {
        &self.bookkeeper
    }
}

/// A temporary struct to for querying/viewing prover round message.
pub struct AtProverRound<'a, F: PrimeField, O: RoundOracle<F>> {
    _self: &'a mut MessagesCollection<F, O>,
    round: MsgRoundRef,
}

impl<'a, F: PrimeField, O: RoundOracle<F>> AtProverRound<'a, F, O> {
    /// Return the leaves of at `position` of all oracle in this round.
    /// `result[i][j]` is leaf `i` at oracle `j`.
    pub fn query_point(&mut self, positions: &[usize], tracer: TraceInfo) -> Vec<Vec<F>> {
        let _self = &mut self._self;
        let round = self.round;
        if !round.is_virtual {
            info!("Query Real Oracle point at {:?} by {}", positions, tracer);
            return _self.real_oracles[round.index].query(positions);
        }

        info!(
            "Query Virtual Oracle point at {:?} by {}",
            positions, tracer
        );

        let (virtual_round, mut shadow_self) = _self.take_virtual_oracle(round);

        let query_result = virtual_round.query_point(positions, &mut shadow_self);

        // restore self
        _self.restore_from_shadow_self(shadow_self, round, virtual_round);

        // return the query result
        query_result
    }

    /// Return the queried coset at `coset_index` of all oracles in this round.
    /// `result[i][j][k]` is coset index `i` -> oracle index `j` -> element `k`
    /// in this coset.
    pub fn query_coset(&mut self, positions: &[usize], tracer: TraceInfo) -> CosetQueryResult<F> {
        let _self = &mut self._self;
        let round = self.round;
        if !round.is_virtual {
            info!("Query Real Oracle coset at {:?} by {}", positions, tracer);
            return _self.real_oracles[round.index].query_coset(positions);
        }

        let (virtual_round, mut shadow_self) = _self.take_virtual_oracle(round);

        info!(
            "Query Virtual Oracle coset at {:?} by {}",
            positions, tracer
        );
        let query_result = virtual_round.query_coset(positions, &mut shadow_self);

        // restore self
        _self.restore_from_shadow_self(shadow_self, round, virtual_round);

        // return the query result
        query_result
    }

    /// Return the short message at a prover round
    pub fn short_message(&self, index: usize, tracer: TraceInfo) -> &[F] {
        let at = self.round;
        info!("Get prover short message by {}", tracer);
        if at.is_virtual {
            unimplemented!("Virtual oracle does not have short message");
        } else {
            self._self.real_oracles[at.index].get_short_message(index)
        }
    }
}

/// The result of a coset query. `result[i][j][k]` is coset index `i` -> oracle
/// index `j` -> element `k`
#[repr(transparent)]
pub struct CosetQueryResult<T: Clone>(pub Vec<Vec<Vec<T>>>);

impl<T: Clone> CosetQueryResult<T> {
    /// `result[i][j]` is coset index `coset_index` -> oracle index `i` ->
    /// element `j`
    pub fn at_coset_index(&self, coset_index: usize) -> &[Vec<T>] {
        &self.0[coset_index]
    }

    /// `result[i][j]` is coset index `coset_index` -> oracle index
    /// `oracle_index` -> element `j`
    pub fn at_oracle_index(&self, oracle_index: usize) -> impl Iterator<Item = &Vec<T>> {
        self.0.iter().map(move |coset| &coset[oracle_index])
    }

    /// `result[i][j]` is coset index `coset_index` -> oracle index
    /// `oracle_index` -> element `j`
    pub(crate) fn take_oracle_index(
        &mut self,
        oracle_index: usize,
    ) -> Vec<Vec<T>> {
        self.0.iter_mut().map(move |coset| ark_std::mem::take(&mut coset[oracle_index])).collect()
    }

    /// `result[i][j]` is coset index `coset_index` -> oracle index
    /// `oracle_index` -> element `j`
    pub fn at_oracle_index_owned(self, oracle_index: usize) -> impl Iterator<Item = Vec<T>> {
        self.0
            .into_iter()
            .map(move |coset| coset[oracle_index].to_vec())
    }

    /// assume this query response has only one coset query, return this coset
    /// result. `result[i]` is coset evaluations of oracle `i`.
    pub fn assume_single_coset(mut self) -> Vec<Vec<T>> {
        assert_eq!(self.0.len(), 1);
        self.0.pop().unwrap()
    }

    /// assume this query response has only one oracle, return this coset
    /// result. `result[i]` is coset evaluations of coset `i`.
    pub fn assume_single_oracle(self) -> Vec<Vec<T>> {
        self.0
            .into_iter()
            .map(|mut coset_eval| {
                assert_eq!(coset_eval.len(), 1, "has multiple oracle evaluations");
                coset_eval.pop().unwrap()
            })
            .collect()
    }

    /// iterate over coset index. For each element, `element[i][j]` is oracle
    /// index `i` -> element `j`
    pub fn iter(&self) -> impl Iterator<Item = &Vec<Vec<T>>> {
        self.0.iter()
    }

    /// number of cosets
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Return `self` query_result of a single oracle.
    /// `query_result[i][j]` is coset index `i` -> element `j`. The shape of returned result will be `(num_cosets, 1, coset_size)`
    pub fn from_single_oracle_result(query_result: Vec<Vec<T>>) -> Self {
        query_result.into_iter().map(|coset| vec![coset]).collect()
    }
}

impl<T: Clone> From<Vec<Vec<Vec<T>>>> for CosetQueryResult<T> {
    fn from(v: Vec<Vec<Vec<T>>>) -> Self {
        Self(v)
    }
}

impl<T: Clone> FromIterator<Vec<Vec<T>>> for CosetQueryResult<T> {
    fn from_iter<I: IntoIterator<Item = Vec<Vec<T>>>>(iter: I) -> Self {
        // item is evaluation of multiple oracles on one coset
        Self(iter.into_iter().collect())
    }
}

impl<T: Clone> IntoIterator for CosetQueryResult<T> {
    type Item = Vec<Vec<T>>;
    type IntoIter = ark_std::vec::IntoIter<Vec<Vec<T>>>;

    /// iterate over coset index. For each element, `element[i][j]` is oracle
    /// index `i` -> element `j`
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

/// If the leaf is coset, the info also contains information about the stride of
/// coset, and each leaf will be a flattened 2d array where first axis is oracle
/// index, and second axis is leaf positions.
///
/// For example, if the coset is `[3,6,9]` and we have 2 oracles, then the leaf
/// will be `[oracle[0][3], oracle[0][6], oracle[0][9], oracle[1][3],
/// oracle[1][6], oracle[1][9]]`

/// Contains structure and degree bound information about prover round messages,
/// but does not contain real messages.
#[derive(Eq, PartialEq, Debug, Clone)]
pub struct ProverRoundMessageInfo {
    /// Degree bounds of oracle evaluations, in order.
    pub reed_solomon_code_degree_bound: Vec<usize>,
    /// Number of message oracles without degree bound. Those oracles will not
    /// be processed by LDT.
    pub num_message_oracles: usize,
    /// Number of short messages. Those messages will be included in proof in
    /// entirety.
    pub num_short_messages: usize,
    /// The type of leaves: whether it uses codeword domain or custom length and localization.
    pub leaves_type: LeavesType,
    /// Number of elements in each oracle in this round.
    pub length: usize,
    /// Localization parameter for this round. When serializing to a merkle tree, each leaf is a hash of `2 ^ localization_parameter` elements.
    /// For example, if we have elements `[1,2,3,4,5,6,7,8]` and localization parameter is 1, then the serialized merkle tree leaves will be
    /// `[H(1,5), H(2,6), H(3,7), H(4,8)]`.   
    pub localization_parameter: usize,
}

/// Builds a `ProverRoundMessageInfo` from a `ProverRoundMessageInfoBuilder`.
pub struct ProverRoundMessageInfoBuilder {
    reed_solomon_code_degree_bound: Vec<usize>,
    num_message_oracles: usize,
    num_short_messages: usize,
    length: usize,
    localization_parameter: usize,
    leaves_type: LeavesType,
}

impl ProverRoundMessageInfo {
    /// Create a builder for prover round message info.
    /// * `leaves_options`: `UseCodewordDomain | Custom`
    /// * `length`: length of codeword
    /// * `localization_parameter`: localization parameter
    pub fn new(
        leaves_options: LeavesType,
        length: usize,
        localization_parameter: usize,
    ) -> ProverRoundMessageInfoBuilder {
        ProverRoundMessageInfoBuilder {
            reed_solomon_code_degree_bound: vec![],
            num_message_oracles: 0,
            num_short_messages: 0,
            leaves_type: leaves_options,
            length,
            localization_parameter,
        }
    }

    /// Builds prover round message info using codeword domain.
    pub fn new_using_codeword_domain<P, S, F>(
        transcript: &mut SimulationTranscript<P, S, F>,
    ) -> ProverRoundMessageInfoBuilder
    where
        P: Config<Leaf = [F]>,
        S: CryptographicSponge,
        F: PrimeField + Absorb,
        P::InnerDigest: Absorb,
    {
        let length = transcript
            .ldt_codeword_domain
            .expect("codeword domain not set")
            .size();
        let localization_parameter = transcript
            .ldt_localization_parameter
            .expect("codeword localization parameter not set");
        Self::new(UseCodewordDomain, length, localization_parameter)
    }

    /// Builds prover round message info using custom length and localization.
    pub fn new_using_custom_length_and_localization(
        length: usize,
        localization_parameter: usize,
    ) -> ProverRoundMessageInfoBuilder {
        Self::new(Custom, length, localization_parameter)
    }
}

impl ProverRoundMessageInfoBuilder {
    /// Degree bounds of oracle evaluations, in order.
    pub fn with_reed_solomon_codes_degree_bounds(mut self, degrees: Vec<usize>) -> Self {
        if self.leaves_type == Custom {
            panic!("Cannot set oracle with degree bounds when leaves_options is Custom");
        }
        self.reed_solomon_code_degree_bound = degrees;
        self
    }
    /// Number of message oracles without degree bound. Those oracles will not
    /// be processed by LDT.
    pub fn with_num_message_oracles(mut self, num: usize) -> Self {
        self.num_message_oracles = num;
        self
    }
    /// Number of short messages. Those messages will be included in proof in
    /// entirety.
    pub fn with_num_short_messages(mut self, num: usize) -> Self {
        self.num_short_messages = num;
        self
    }

    /// Builds a `ProverRoundMessageInfo` from this builder.
    pub fn build(self) -> ProverRoundMessageInfo {
        ProverRoundMessageInfo {
            reed_solomon_code_degree_bound: self.reed_solomon_code_degree_bound,
            num_message_oracles: self.num_message_oracles,
            num_short_messages: self.num_short_messages,
            leaves_type: self.leaves_type,
            length: self.length,
            localization_parameter: self.localization_parameter,
        }
    }
}

/// Specify the length and localization parameter of an oracle.
#[derive(Eq, PartialEq, Debug, Clone, Copy)]
pub enum LeavesType {
    /// Indicates that this round message uses same domain as codeword domain.
    UseCodewordDomain,
    /// Indicates that this round message uses custom length and localization.
    /// In this case, oracles with degree bound cannot be used in this round.
    Custom,
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
    /// If `self` contains field elements, return those elements. Otherwise
    /// return `None`.
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
