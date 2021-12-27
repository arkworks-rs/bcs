use crate::{bcs::MTHashParameters, iop::bookkeeper::MessageBookkeeper, tracer::TraceInfo, Error};
use ark_crypto_primitives::{merkle_tree::Config as MTConfig, MerkleTree};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_std::vec::Vec;
use tracing::info;

use super::{
    bookkeeper::{BookkeeperContainer, ToMsgRoundRef},
    oracles::{RecordingRoundOracle, RoundOracle, VirtualOracle},
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
    pub(crate) virtual_oracles: Vec<Option<VirtualOracle<F, O>>>,
    pub(crate) verifier_messages: Vec<Vec<VerifierMessage<F>>>,
    pub(crate) bookkeeper: MessageBookkeeper,
}

impl<F: PrimeField, O: RoundOracle<F>> MessagesCollection<F, O> {
    pub(crate) fn new(
        real_oracles: Vec<O>,
        virtual_oracles: Vec<Option<VirtualOracle<F, O>>>,
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
    fn take_virtual_oracle(&mut self, round: MsgRoundRef) -> (VirtualOracle<F, O>, Self) {
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
        vo: VirtualOracle<F, O>,
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
    pub fn query_coset(&mut self, positions: &[usize], tracer: TraceInfo) -> Vec<Vec<Vec<F>>> {
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

pub(crate) struct PendingProverMessage<F: PrimeField> {
    /// Oracle evaluations with a degree bound.
    pub(crate) reed_solomon_codes: Vec<(Vec<F>, usize)>,
    /// Message oracles without a degree bound
    pub(crate) message_oracles: Vec<Vec<F>>,
    /// Messages without oracle sent in current round
    pub(crate) short_messages: Vec<Vec<F>>,
    /// length of each oracle message. `oracle_length` is 0 if in this round,
    /// prover sends only short messages.
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
    /// For example, if the coset is `[3,6,9]` and we have 2 oracles, then the
    /// leaf will be `[oracle[0][3], oracle[0][6], oracle[0][9],
    /// oracle[1][3], oracle[1][6], oracle[1][9]]`
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
            message_oracles: self.message_oracles,
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

/// If the leaf is coset, the info also contains information about the stride of
/// coset, and each leaf will be a flattened 2d array where first axis is oracle
/// index, and second axis is leaf positions.
///
/// For example, if the coset is `[3,6,9]` and we have 2 oracles, then the leaf
/// will be `[oracle[0][3], oracle[0][6], oracle[0][9], oracle[1][3],
/// oracle[1][6], oracle[1][9]]`

/// Contains structure and degree bound information about prover round messages,
/// but does not contain real messages.
#[derive(Eq, PartialEq, Debug, Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProverRoundMessageInfo {
    /// Degree bounds of oracle evaluations, in order.
    pub reed_solomon_code_degree_bound: Vec<usize>,
    /// Number of message oracles without degree bound. Those oracles will not
    /// be processed by LDT.
    pub num_message_oracles: usize,
    /// Number of short messages. Those messages will be included in proof in
    /// entirety.
    pub num_short_messages: usize,
    /// Length of each message oracles in current round.
    pub oracle_length: usize,
    /// log2(coset size)
    /// Set it to zero to disable leaf as coset.
    pub localization_parameter: usize,
}

impl ProverRoundMessageInfo {
    /// Return a new round message information.
    pub fn new(
        reed_solomon_code_degree_bound: Vec<usize>,
        num_message_oracles: usize,
        num_short_messages: usize,
        oracle_length: usize,
        localization_parameter: usize,
    ) -> Self {
        ProverRoundMessageInfo {
            reed_solomon_code_degree_bound,
            num_message_oracles,
            num_short_messages,
            oracle_length,
            localization_parameter,
        }
    }
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
