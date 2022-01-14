use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};
use ark_std::vec::Vec;
use tracing::info;

use crate::iop::message::LeavesType;
use crate::iop::message::LeavesType::{Custom, UseCodewordDomain};
use crate::{
    bcs::MTHashParameters,
    iop::{
        bookkeeper::{MessageBookkeeper, NameSpace, ToMsgRoundRef},
        message::{MsgRoundRef, ProverRoundMessageInfo, VerifierMessage},
        oracles::{
            CosetEvaluator, RecordingRoundOracle, RoundOracle, SuccinctRoundMessage, VirtualOracle,
        },
    },
    tracer::TraceInfo,
    Error,
};
use ark_crypto_primitives::MerkleTree;
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::{univariate::DensePolynomial, Polynomial};
use ark_std::mem::take;

#[allow(variant_size_differences)]
/// Pending message for current transcript. We allow `variant_size_differences`
/// here because there will only be one `PendingMessage` per transcript.
enum PendingMessage<F: PrimeField + Absorb> {
    VerifierMessage(Vec<VerifierMessage<F>>),
    None,
}

impl<F: PrimeField + Absorb> Default for PendingMessage<F> {
    fn default() -> Self {
        Self::None
    }
}

/// A communication protocol for IOP prover.
pub struct Transcript<P: MTConfig<Leaf = [F]>, S: CryptographicSponge, F: PrimeField + Absorb>
where
    P::InnerDigest: Absorb,
{
    /// merkle tree hash parameters
    pub hash_params: MTHashParameters<P>,
    /// Messages sent by prover in commit phase. Each item in the vector
    /// represents a list of message oracles with same length. The length
    /// constraints do not hold for short messages (IP message). All non-IP
    /// messages in the same prover round should share the same merkle tree.
    /// Each merkle tree leaf is a vector which each element correspond to
    /// the same location of different oracles
    pub prover_message_oracles: Vec<RecordingRoundOracle<F>>,
    /// Virtual oracle registered during commit phase simulation.
    /// The second element of each tuple has shape `(num_oracles,
    /// codeword_size)`
    pub(crate) registered_virtual_oracles:
        Vec<(VirtualOracle<F, RecordingRoundOracle<F>>, Vec<Vec<F>>)>,
    /// Each element `merkle_tree_for_each_round[i]` corresponds to the merkle
    /// tree for `prover_message_oracles[i]`. If no oracle messages in this
    /// round, merkle tree will be `None`.
    pub merkle_tree_for_each_round: Vec<Option<MerkleTree<P>>>,
    /// Sampled Message sent by verifier in commit phase. In each round,
    /// verifier can send multiple messages.
    pub verifier_messages: Vec<Vec<VerifierMessage<F>>>,
    /// bookkeepers for messages in different subprotocols
    pub(crate) bookkeeper: MessageBookkeeper,
    /// Random Oracle to sample verifier messages.
    pub sponge: S,
    pending_message_for_current_round: PendingMessage<F>,
    pub(crate) ldt_codeword_domain: Option<Radix2CosetDomain<F>>,
    pub(crate) ldt_localization_parameter: Option<usize>,
}

impl<P, S, F> Transcript<P, S, F>
where
    P: MTConfig<Leaf = [F]>,
    S: CryptographicSponge,
    F: PrimeField + Absorb,
    P::InnerDigest: Absorb,
{
    /// Return a new BCS transcript.
    pub fn new(
        sponge: S,
        hash_params: MTHashParameters<P>,
        ldt_codeword_domain: Option<Radix2CosetDomain<F>>,
        ldt_localization_parameter: Option<usize>,
        trace: TraceInfo,
    ) -> Self {
        Self {
            prover_message_oracles: Vec::new(),
            merkle_tree_for_each_round: Vec::new(),
            verifier_messages: Vec::new(),
            bookkeeper: MessageBookkeeper::new(trace),
            sponge,
            hash_params,
            pending_message_for_current_round: PendingMessage::default(),
            ldt_codeword_domain,
            ldt_localization_parameter,
            registered_virtual_oracles: Vec::new(),
        }
    }

    /// Create a new namespace in bookkeeper.
    pub fn new_namespace(&mut self, current_namespace: NameSpace, trace: TraceInfo) -> NameSpace {
        self.bookkeeper.new_namespace(trace, current_namespace.id)
    }

    /// Add a prover round, using codeword domain.
    /// TODO: add an example here
    pub fn add_prover_round_with_codeword_domain(&mut self) -> PendingProverMessage<P, S, F> {
        let oracle_length = self.codeword_domain().size();
        let localization_parameter = self.codeword_localization_parameter();
        PendingProverMessage {
            reed_solomon_codes: Vec::new(),
            message_oracles: Vec::new(),
            short_messages: Vec::new(),
            transcript: self,
            leaves_type: UseCodewordDomain,
            oracle_length,
            localization_parameter,
        }
    }

    /// Add a prover round, using custom length and localization.
    /// TODO: add an example here
    pub fn add_prover_round_with_custom_length_and_localization(
        &mut self,
        length: usize,
        localization_parameter: usize,
    ) -> PendingProverMessage<P, S, F> {
        PendingProverMessage {
            reed_solomon_codes: Vec::new(),
            message_oracles: Vec::new(),
            short_messages: Vec::new(),
            transcript: self,
            leaves_type: Custom,
            oracle_length: length,
            localization_parameter,
        }
    }

    /// Register a virtual oracle specfied by coset evaluator.
    /// * `coset_query_evaluator`: a function that takes a coset and constituent
    ///   oracles, and return query responses
    /// * `evaluation_on_domain`: evaluation of this virtual round on evaluation
    ///   domain. `evaluation_on_domain[i]` is the evaluation of ith oracle at
    ///   this round.
    pub fn register_prover_virtual_round(
        &mut self,
        ns: NameSpace,
        coset_query_evaluator: CosetEvaluator<F, RecordingRoundOracle<F>>,
        evaluations_on_domain: Vec<Vec<F>>,
        test_bound: Vec<usize>,
        constraint_bound: Vec<usize>,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        info!("Register prover virtual oracle: {}", trace);
        // make sure that we are not in midway of a round
        assert!(!self.is_pending_message_available());

        let (codeword_domain, localization_param) = (
            self.codeword_domain(),
            self.codeword_localization_parameter(),
        );

        // make sure all oracles in `evaluation_on_domain` has the same length as the
        // size of `codeword_domain`
        assert!(
            evaluations_on_domain
                .iter()
                .all(|x| x.len() == codeword_domain.size()),
            "All oracles in evaluation_on_domain should have the same length as the size of \
             codeword_domain"
        );

        let virtual_oracle = VirtualOracle::new(
            coset_query_evaluator,
            codeword_domain,
            localization_param,
            test_bound,
            constraint_bound,
        );

        self.registered_virtual_oracles
            .push((virtual_oracle, evaluations_on_domain));
        self.attach_latest_prover_round_to_namespace(ns, true, trace)
    }

    /// Access previously received verifier round using a reference. This
    /// function is useful when the prover wants to have access to messages
    /// sent from other protocols.
    ///
    /// TODO: rethink about this because we have virtual oracle.
    /// Probably we can have `get_previously_sent_codeword` (panic if virtual),
    /// and `get_previously_sent_prover_round_info`
    pub fn get_previously_sent_prover_round(
        &self,
        msg_ref: impl ToMsgRoundRef,
    ) -> &RecordingRoundOracle<F> {
        let msg_ref = msg_ref.to_prover_msg_round_ref(&self.bookkeeper);
        if !msg_ref.is_virtual {
            &self.prover_message_oracles[msg_ref.index]
        } else {
            panic!("This round is virtual. ")
        }
    }

    /// Get low-degree oracle evaluations at index `x` or requested round.
    ///
    /// For example, if in requested round, prover send low-degree oracle `[p0,
    /// p1, p2, ...]`, non low-degree oracle `[q0, q1, ...]`,
    /// `get_previously_sent_prover_rs_code(at, index)` will return evaluation
    /// of `p_index` at domain.
    pub fn get_previously_sent_prover_rs_code(&self, at: impl ToMsgRoundRef, index: usize) -> &[F] {
        let msg_ref = at.to_prover_msg_round_ref(&self.bookkeeper);
        if msg_ref.is_virtual {
            &self.registered_virtual_oracles[msg_ref.index].1[index]
        } else {
            &self.prover_message_oracles[msg_ref.index].reed_solomon_codes[index].0
        }
    }

    /// Get all low-degree oracle evaluations at  requested round.
    ///
    /// For example, if in requested round, prover send low-degree oracle `[p0,
    /// p1, p2, ...]`, non low-degree oracle `[q0, q1, ...]`,
    /// `get_previously_sent_prover_rs_code(at)` will return evaluation
    /// of `[p0, p1, p2, ...]` at domain.
    pub fn get_previous_sent_prover_rs_codes(&self, at: impl ToMsgRoundRef) -> Vec<Vec<F>> {
        let msg_ref = at.to_prover_msg_round_ref(&self.bookkeeper);
        if msg_ref.is_virtual {
            self.registered_virtual_oracles[msg_ref.index].1.clone()
        } else {
            self.prover_message_oracles[msg_ref.index]
                .reed_solomon_codes
                .iter()
                .map(|x| &x.0)
                .cloned()
                .collect()
        }
    }

    /// Get information about the requested round.
    pub fn get_previously_sent_prover_round_info(
        &self,
        at: impl ToMsgRoundRef,
    ) -> ProverRoundMessageInfo {
        let msg_ref = at.to_prover_msg_round_ref(&self.bookkeeper);
        if msg_ref.is_virtual {
            self.registered_virtual_oracles[msg_ref.index].0.get_info()
        } else {
            self.prover_message_oracles[msg_ref.index].get_info()
        }
    }

    /// Access previously received verifier round using a reference. This
    /// function is useful when the prover wants to have access to messages
    /// sent from other protocols.
    pub fn get_previously_received_verifier_round(
        &self,
        msg_ref: MsgRoundRef,
    ) -> &Vec<VerifierMessage<F>> {
        &self.verifier_messages[msg_ref.index]
    }

    /// Submit all verifier messages in this round, and set pending round
    /// message to `None`. # Panic
    /// Panic if current verifier round messages is `None` or `ProverMessage`
    pub fn submit_verifier_current_round(
        &mut self,
        namespace: NameSpace,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        info!("verifier round: {}", trace);

        let pending_message = take(&mut self.pending_message_for_current_round);
        if let PendingMessage::VerifierMessage(round_msg) = pending_message {
            self.verifier_messages.push(round_msg);
            self.attach_latest_verifier_round_to_namespace(namespace, trace)
        } else {
            unreachable!() // TODO: refactor PendingMessage structure
        }
    }

    /// Squeeze sampled verifier message as field elements. The squeezed
    /// elements is attached to pending messages, and need to be submitted
    /// through `submit_verifier_current_round`. Submitted messages will be
    /// stored in transcript and will be later given to verifier in query
    /// and decision phase.
    pub fn squeeze_verifier_field_elements(&mut self, field_size: &[FieldElementSize]) -> Vec<F> {
        // squeeze message
        let msg = self.sponge.squeeze_field_elements_with_sizes(field_size);
        // store the verifier message for later decision phase
        self.current_verifier_pending_message()
            .push(VerifierMessage::FieldElements(msg.clone()));
        msg
    }

    /// Squeeze sampled verifier message as bytes. The squeezed elements is
    /// attached to pending messages, and need to be submitted through
    /// `submit_verifier_current_round`. Submitted messages will be stored in
    /// transcript and will be later given to verifier in query and decision
    /// phase.
    pub fn squeeze_verifier_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        // squeeze message
        let msg = self.sponge.squeeze_bytes(num_bytes);
        // store the verifier message for later decision phase
        self.current_verifier_pending_message()
            .push(VerifierMessage::Bytes(msg.clone()));
        msg
    }

    /// Squeeze sampled verifier message as bits. The squeezed elements is
    /// attached to pending messages, and need to be submitted through
    /// `submit_verifier_current_round`. Submitted messages will be stored in
    /// transcript and will be later given to verifier in query and decision
    /// phase.
    pub fn squeeze_verifier_bits(&mut self, num_bits: usize) -> Vec<bool> {
        // squeeze message
        let msg = self.sponge.squeeze_bits(num_bits);
        // store the verifier message for later decision phase
        self.current_verifier_pending_message()
            .push(VerifierMessage::Bits(msg.clone()));
        msg
    }

    /// Returns if there is a pending message for the transcript.
    pub fn is_pending_message_available(&self) -> bool {
        if let PendingMessage::None = self.pending_message_for_current_round {
            return false;
        }
        return true;
    }

    #[allow(unused)]
    pub(crate) fn all_succinct_messages(&self) -> Vec<SuccinctRoundMessage<F>> {
        self.prover_message_oracles
            .iter()
            .map(|round| round.get_succinct())
            .collect::<Vec<_>>()
    }

    #[allow(dead_code)]
    pub(crate) fn merkle_tree_roots(&self) -> Vec<Option<P::InnerDigest>> {
        self.merkle_tree_for_each_round
            .iter()
            .map(|mt_| mt_.as_ref().map(|mt| mt.root()))
            .collect::<Vec<_>>()
    }

    /// Get reference to current verifier pending message.
    /// If current round pending message to `None`, current round message will
    /// become verifier message type. Panic if current pending message is
    /// not verifier message.
    fn current_verifier_pending_message(&mut self) -> &mut Vec<VerifierMessage<F>> {
        if let PendingMessage::None = &self.pending_message_for_current_round {
            self.pending_message_for_current_round = PendingMessage::VerifierMessage(Vec::new());
        }
        match &mut self.pending_message_for_current_round {
            PendingMessage::VerifierMessage(msg) => msg,
            PendingMessage::None => unreachable!(),
        }
    }

    fn attach_latest_prover_round_to_namespace(
        &mut self,
        namespace: NameSpace,
        is_virtual: bool,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        // add verifier message index to namespace
        let index = if is_virtual {
            self.registered_virtual_oracles.len() - 1
        } else {
            self.prover_message_oracles.len() - 1
        };
        self.bookkeeper
            .attach_prover_round_to_namespace(namespace, index, is_virtual, trace)
    }

    fn attach_latest_verifier_round_to_namespace(
        &mut self,
        namespace: NameSpace,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        // add verifier message index to namespace
        let index = self.verifier_messages.len() - 1;
        self.bookkeeper
            .attach_verifier_round_to_namespace(namespace, index, trace)
    }
}

/// An temporary struct to hold the message for current round.
pub struct PendingProverMessage<'a, P, S, F>
where
    P: MTConfig<Leaf = [F]>,
    S: CryptographicSponge,
    F: PrimeField + Absorb,
    P::InnerDigest: Absorb,
{
    /// Oracle evaluations with a degree bound. For now, it is required that all `reed_solomon_codes` have the same domain as codeword domain.  
    reed_solomon_codes: Vec<(Vec<F>, usize)>,
    /// Message oracles without a degree bound.
    message_oracles: Vec<Vec<F>>,
    /// Messages without oracle sent in current round. There is no constraint on the length of the messages.
    short_messages: Vec<Vec<F>>,
    transcript: &'a mut Transcript<P, S, F>,
    leaves_type: LeavesType,
    oracle_length: usize,
    localization_parameter: usize,
}

impl<'a, P, S, F> PendingProverMessage<'a, P, S, F>
where
    P: MTConfig<Leaf = [F]>,
    S: CryptographicSponge,
    F: PrimeField + Absorb,
    P::InnerDigest: Absorb,
{
    /// Send Reed-Solomon codes of a polynomial.
    /// For now, it is required that all `reed_solomon_codes` have LDT codeword domain.
    /// # Panics
    /// - Panics if current round is using custom length and localization.
    /// - Panics if message length is not equal to domain size.
    pub fn send_oracle_evaluations_with_degree_bound(
        mut self,
        msg: impl IntoIterator<Item = F>,
        degree_bound: usize,
    ) -> Self {
        assert_eq!(
            self.leaves_type, UseCodewordDomain,
            "Cannot send RS-code with degree bound using custom length and localization."
        );
        let oracle = msg.into_iter().collect::<Vec<_>>();
        assert_eq!(oracle.len(), self.transcript.codeword_domain().size());
        self.reed_solomon_codes.push((oracle, degree_bound));
        self
    }

    /// Send prover message oracles. For now, it is required that all `message_oracles` have the same length as the domain size.
    /// Also, the localization parameter of the oracles will be determined by transcript.
    /// # Panics
    ///  Panics if the length of oracle message is not equal to length for current round.
    pub fn send_oracle_message_without_degree_bound(
        mut self,
        msg: impl IntoIterator<Item = F>,
    ) -> Self {
        let oracle: Vec<_> = msg.into_iter().collect();
        assert_eq!(oracle.len(), self.oracle_length);
        self.message_oracles.push(oracle);
        self
    }

    /// Send short message that does not need to be an oracle. The entire
    /// message will be included in BCS proof, and no merkle tree will be
    /// generated. There is no constraint on the length of the messages.
    pub fn send_short_message(mut self, msg: impl IntoIterator<Item = F>) -> Self {
        let msg: Vec<_> = msg.into_iter().collect();
        self.short_messages.push(msg);
        self
    }

    /// Send univariate polynomial with LDT.
    /// Evaluation domain and localization parameter is managed by LDT.
    ///
    /// # Panics
    /// This function panics if polynomial's degree is larger than degree bound.
    pub fn send_univariate_polynomial(
        self,
        poly: &DensePolynomial<F>,
        degree_bound: usize,
    ) -> Self {
        // check degree bound
        assert!(
            poly.degree() <= degree_bound,
            "polynomial degree is larger than degree bound"
        );
        // evaluate the poly using ldt domain
        let evaluations = self.transcript.codeword_domain().evaluate(poly);
        self.send_oracle_evaluations_with_degree_bound(evaluations, degree_bound)
    }

    /// Submit current round to transcript.
    pub fn submit(self, namespace: NameSpace, trace: TraceInfo) -> Result<MsgRoundRef, Error> {
        // generate merkle tree
        // extract short messages
        let (mt, recording_oracle, transcript) = self.into_merkle_tree_and_recording_oracle()?;
        // if this round prover message contains oracle messages, absorb merkle tree
        // root
        transcript.sponge.absorb(&mt.as_ref().map(|x| x.root()));
        // if this round prover message has non-oracle messages, absorb them in entirety
        recording_oracle
            .short_messages
            .iter()
            .for_each(|msg| transcript.sponge.absorb(msg));
        transcript.prover_message_oracles.push(recording_oracle);
        transcript.merkle_tree_for_each_round.push(mt);

        Ok(transcript.attach_latest_prover_round_to_namespace(namespace, false, trace))
    }

    fn has_oracle(&self) -> bool {
        !self.reed_solomon_codes.is_empty() || !self.message_oracles.is_empty()
    }

    /// Generate a merkle tree of `Self` where each leaf is a coset.
    /// For example, if the coset is `[3,6,9]` and we have 2 oracles, then the
    /// leaf will be `[oracle[0][3], oracle[0][6], oracle[0][9],
    /// oracle[1][3], oracle[1][6], oracle[1][9]]`
    fn into_merkle_tree_and_recording_oracle(
        self, // all RS-codes, all message oracles
    ) -> Result<
        (
            Option<MerkleTree<P>>,
            RecordingRoundOracle<F>,
            &'a mut Transcript<P, S, F>,
        ),
        Error,
    > {
        let hash_params = &self.transcript.hash_params;
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
            reed_solomon_code_degree_bound: self
                .reed_solomon_codes
                .iter()
                .map(|(_, degree)| *degree)
                .collect(),
            num_short_messages: self.short_messages.len(),
            num_message_oracles: self.message_oracles.len(),
            leaves_type: self.leaves_type,
            length: self.oracle_length,
            localization_parameter: self.localization_parameter,
        };
        let recording_oracle = RecordingRoundOracle {
            info,
            reed_solomon_codes: self.reed_solomon_codes,
            message_oracles: self.message_oracles,
            short_messages: self.short_messages,
            all_coset_elements,
            queried_coset_index: Vec::new(),
        };
        Ok((mt, recording_oracle, self.transcript))
    }

    /// Generate a un-flattened merkle tree leaves
    ///
    /// result axes:`[coset index, oracle index, element index in coset]`
    fn generate_all_cosets(&self) -> Vec<Vec<Vec<F>>> {
        if !self.has_oracle() {
            return Vec::new();
        }
        let oracle_length = self.oracle_length;
        let localization_parameter = self.localization_parameter;
        let coset_size = 1 << localization_parameter;
        debug_assert_eq!(oracle_length % coset_size, 0);
        let num_cosets = oracle_length / coset_size;
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

impl<P: MTConfig<Leaf = [F]>, S: CryptographicSponge, F: PrimeField + Absorb> LDTInfo<F>
    for Transcript<P, S, F>
where
    P::InnerDigest: Absorb,
{
    fn codeword_domain(&self) -> Radix2CosetDomain<F> {
        self.ldt_codeword_domain.expect("LDT not enabled")
    }

    fn codeword_localization_parameter(&self) -> usize {
        self.ldt_localization_parameter
            .expect("LDT not enabled or localization parameter is not supported by LDT")
    }
}

/// A wrapper trait for transcript that contains LDT information. This trait is
/// used to get LDT codeword domain and localization parameter, and is designed
/// to reduce code duplication.
pub trait LDTInfo<F: PrimeField> {
    /// Return the codeword domain used by LDT.
    ///
    /// **Any low degree oracle will use this domain as evaluation domain.**
    ///
    /// ## Panics
    /// This function panics if LDT is not enabled.
    fn codeword_domain(&self) -> Radix2CosetDomain<F>;

    /// Return the localization parameter used by LDT. Localization parameter is
    /// the size of query coset of the codeword.
    ///
    /// ## Panics
    /// This function panics if LDT is not enabled or localization parameter is
    /// not supported by LDT.
    fn codeword_localization_parameter(&self) -> usize;

    /// Given the coset index, return the corresponding query coset of the LDT.
    ///
    /// For example, if the codeword domain is `{a,b,c,d,e,f,g,h}`, and
    /// localization parameter is 2, then this function returns `{a,e}` if the
    /// coset index is 0, `{b,f}` if the coset index is 1, and `{c,g}` if the
    /// coset index is 2, and `{d,h}` if the coset index is 3.
    fn ldt_codeword_query_coset(&self, coset_index: usize) -> Radix2CosetDomain<F> {
        let (codeword_domain, localization_param) = (
            self.codeword_domain(),
            self.codeword_localization_parameter(),
        );
        codeword_domain
            .query_position_to_coset(coset_index, localization_param)
            .1
    }
}
