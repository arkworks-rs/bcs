use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};
use ark_std::vec::Vec;
use tracing::info;

use crate::{
    bcs::{prover::BCSProof, MTHashParameters},
    iop::{
        message::{
            MsgRoundRef, PendingProverMessage, ProverRoundMessageInfo, ToMsgRoundRef,
            VerifierMessage,
        },
        oracles::{
            CosetEvaluator, RecordingRoundOracle, RoundOracle, SuccinctRoundMessage,
            SuccinctRoundOracle, VirtualOracle,
        },
    },
    tracer::TraceInfo,
    Error,
};
use ark_crypto_primitives::MerkleTree;
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::{univariate::DensePolynomial, Polynomial};
use ark_std::mem::take;

use super::bookkeeper::{MessageBookkeeper, NameSpace};

#[allow(variant_size_differences)]
/// Pending message for current transcript. We allow `variant_size_differences`
/// here because there will only be one `PendingMessage` per transcript.
enum PendingMessage<F: PrimeField + Absorb> {
    ProverMessage(PendingProverMessage<F>),
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

    /// Submit all prover oracles in this round, and set pending round message
    /// to `None` # Panic
    /// Panic if current prover round messages is `None` or `VerifierMessage`
    pub fn submit_prover_current_round(
        &mut self,
        namespace: NameSpace,
        trace: TraceInfo,
    ) -> Result<MsgRoundRef, Error> {
        info!("prover round: {}", trace);

        let pending_message = take(&mut self.pending_message_for_current_round);
        if let PendingMessage::ProverMessage(round_msg) = pending_message {
            // generate merkle tree
            // extract short messages
            let (mt, recording_oracle) =
                round_msg.into_merkle_tree_and_recording_oracle(&self.hash_params)?;
            // if this round prover message contains oracle messages, absorb merkle tree
            // root
            self.sponge.absorb(&mt.as_ref().map(|x| x.root()));
            // if this round prover message has non-oracle messages, absorb them in entirety
            recording_oracle
                .short_messages
                .iter()
                .for_each(|msg| self.sponge.absorb(msg));
            self.prover_message_oracles.push(recording_oracle);
            self.merkle_tree_for_each_round.push(mt);
            Ok(self.attach_latest_prover_round_to_namespace(namespace, false, trace))
        } else {
            panic!("Current pending message is not prover message!")
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
            self.ldt_codeword_domain(),
            self.ldt_localization_parameter(),
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
        msg_ref: MsgRoundRef,
    ) -> &RecordingRoundOracle<F> {
        if msg_ref.is_virtual {
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
            panic!("Current pending message is not prover message!")
        }
    }

    /// Send univariate polynomial with LDT.
    /// Evaluation domain and localization parameter is managed by LDT.
    pub fn send_univariate_polynomial(
        &mut self,
        degree_bound: usize,
        poly: &DensePolynomial<F>,
    ) -> Result<(), Error> {
        // check degree bound
        if poly.degree() > degree_bound {
            panic!("polynomial degree is greater than degree bound!");
        }
        // evaluate the poly using ldt domain
        let evaluations = self.ldt_codeword_domain().evaluate(poly);
        self.send_oracle_evaluations(evaluations, degree_bound)?;
        Ok(())
    }

    /// Send Reed-Solomon codes of a polynomial.
    /// Evaluation domain of the message should be the codeword domain for LDT.
    pub fn send_oracle_evaluations(
        &mut self,
        msg: impl IntoIterator<Item = F>,
        degree_bound: usize,
    ) -> Result<(), Error> {
        // encode the message
        let oracle = msg.into_iter().collect::<Vec<_>>();
        assert_eq!(oracle.len(), self.ldt_codeword_domain().size());
        self.set_length_and_localization(oracle.len(), self.ldt_localization_parameter());
        self.current_prover_pending_message()
            .reed_solomon_codes
            .push((oracle, degree_bound));
        Ok(())
    }

    /// Send prover message oracles without LDT. Each position will be an
    /// individual leaf (no localization).
    pub fn send_message_oracle(&mut self, msg: impl IntoIterator<Item = F>) -> Result<(), Error> {
        self.send_message_oracle_with_localization(msg, 0)
    }

    /// Send prover message oracles without LDT. Encode each leaf as a coset of
    /// the oracle. `localization_parameter` is log2(size of each coset).
    /// For example, if the oracle is `[0,1,2,3,4,5,6,7]` and
    /// localization_parameter is 1, leaf will be `[[0,4],[1,5],[2,6],[3,
    /// 7]]`. Larger localization parameter leads larger proof size, and
    /// each queried leaf is larger.
    ///
    /// # Panics
    /// All oracles in the same round need to have same length and same
    /// localization parameter. This function will panic if length or
    /// localization parameter is not consistent with previous oracle.
    pub fn send_message_oracle_with_localization(
        &mut self,
        msg: impl IntoIterator<Item = F>,
        localization_parameter: usize,
    ) -> Result<(), Error> {
        // encode the message
        let oracle: Vec<_> = msg.into_iter().collect();
        debug_assert!(oracle.len().is_power_of_two());
        self.set_length_and_localization(oracle.len(), localization_parameter);
        // store the encoded prover message for generating proof
        self.current_prover_pending_message()
            .message_oracles
            .push(oracle);

        Ok(())
    }

    /// Set the oracle length and localization parameter of this round oracle.
    /// # Panics
    /// * This function will panic if current value is inconsistent with
    ///   previously set value.
    /// For example, if first oracle has length 128, and second oracle will have
    /// length 256, this function will panic. Same for localization
    /// parameter.
    ///
    /// * This function will also panic if current pending message is not prover
    ///   message.
    fn set_length_and_localization(&mut self, oracle_length: usize, localization_parameter: usize) {
        let current_prover_pending_message = self.current_prover_pending_message();
        // set if incoming message is the first oracle
        if current_prover_pending_message.reed_solomon_codes.len()
            + current_prover_pending_message.message_oracles.len()
            == 0
        {
            current_prover_pending_message.oracle_length = oracle_length;
            current_prover_pending_message.localization_parameter = localization_parameter;
            return;
        }
        // check consistency
        if oracle_length != current_prover_pending_message.oracle_length {
            panic!("Oracles have different length in one round");
        }
        if localization_parameter != current_prover_pending_message.localization_parameter {
            panic!("oracles have different localization parameter in one round");
        }
    }

    /// Send short message that does not need to be an oracle. The entire
    /// message will be included in BCS proof, and no merkle tree will be
    /// generated.
    pub fn send_message(&mut self, msg: impl IntoIterator<Item = F>)
    where
        F: Absorb,
    {
        let message: Vec<_> = msg.into_iter().collect();
        // store the message
        self.current_prover_pending_message()
            .short_messages
            .push(message);
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

    /// Get reference to current prover pending message.
    /// If current round pending message to `None`, current round message will
    /// become prover message type. Panic if current pending message is not
    /// prover message.
    fn current_prover_pending_message(&mut self) -> &mut PendingProverMessage<F> {
        if let PendingMessage::None = &self.pending_message_for_current_round {
            self.pending_message_for_current_round =
                PendingMessage::ProverMessage(PendingProverMessage::default());
        }
        match &mut self.pending_message_for_current_round {
            PendingMessage::ProverMessage(msg) => msg,
            PendingMessage::VerifierMessage(_) => panic!("Pending message is verifier message"),
            _ => unreachable!(),
        }
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
            PendingMessage::ProverMessage(..) => panic!("Pending message is prover message"),
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

impl<P: MTConfig<Leaf = [F]>, S: CryptographicSponge, F: PrimeField + Absorb> LDTInfo<F>
    for Transcript<P, S, F>
where
    P::InnerDigest: Absorb,
{
    fn ldt_codeword_domain(&self) -> Radix2CosetDomain<F> {
        self.ldt_codeword_domain.expect("LDT not enabled")
    }

    fn ldt_localization_parameter(&self) -> usize {
        self.ldt_localization_parameter
            .expect("LDT not enabled or localization parameter is not supported by LDT")
    }
}

/// A wrapper for BCS proof, so that verifier can reconstruct verifier messages
/// by simulating commit phase easily.
/// TODO: add virtual oracle here
pub struct SimulationTranscript<
    'a,
    P: MTConfig<Leaf = [F]>,
    S: CryptographicSponge,
    F: PrimeField + Absorb,
> where
    P::InnerDigest: Absorb,
{
    /// prover message info used to verify consistency
    pub(crate) prover_messages_info: Vec<ProverRoundMessageInfo>,

    /// For each round submit, absorb merkle tree root first
    prover_mt_roots: &'a [Option<P::InnerDigest>],
    /// After absorb merkle tree root for this round, absorb the short messages
    /// in entirety
    prover_short_messages: Vec<&'a Vec<Vec<F>>>,

    /// sponge is used to sample verifier message
    pub(crate) sponge: S,
    /// the next prover round message to absorb
    pub(crate) current_prover_round: usize,

    /// Those reconstructed messages will be used in query and decision phase
    pub(crate) reconstructed_verifier_messages: Vec<Vec<VerifierMessage<F>>>,

    pending_verifier_messages: Vec<VerifierMessage<F>>,
    pub(crate) bookkeeper: MessageBookkeeper,

    pub(crate) ldt_codeword_domain: Option<Radix2CosetDomain<F>>,
    pub(crate) ldt_localization_parameter: Option<usize>,

    /// Virtual oracle registered during commit phase simulation.  
    pub(crate) registered_virtual_oracles: Vec<VirtualOracle<F, SuccinctRoundOracle<'a, F>>>,
}

impl<'a, P: MTConfig<Leaf = [F]>, S: CryptographicSponge, F: PrimeField + Absorb>
    SimulationTranscript<'a, P, S, F>
where
    P::InnerDigest: Absorb,
{
    /// Returns a wrapper for BCS proof so that verifier can reconstruct
    /// verifier messages by simulating commit phase easily.
    pub(crate) fn new_transcript(
        bcs_proof: &'a BCSProof<P, F>,
        sponge: S,
        ldt_codeword_domain: Option<Radix2CosetDomain<F>>,
        ldt_localization_parameter: Option<usize>,
        trace: TraceInfo,
    ) -> Self {
        let prover_short_messages = bcs_proof
            .prover_iop_messages_by_round
            .iter()
            .map(|msg| &msg.short_messages)
            .collect::<Vec<_>>();

        let prover_messages_info = bcs_proof
            .prover_iop_messages_by_round
            .iter()
            .map(|msg| msg.get_view().get_info())
            .collect::<Vec<_>>();

        Self {
            prover_short_messages,
            prover_messages_info,
            ldt_codeword_domain,
            ldt_localization_parameter,
            sponge,
            current_prover_round: 0,
            prover_mt_roots: &bcs_proof.prover_messages_mt_root,
            reconstructed_verifier_messages: Vec::new(),
            pending_verifier_messages: Vec::new(),
            bookkeeper: MessageBookkeeper::new(trace),
            registered_virtual_oracles: Vec::new(),
        }
    }

    /// Create a new namespace in bookkeeper.
    pub fn new_namespace(&mut self, current_namespace: NameSpace, trace: TraceInfo) -> NameSpace {
        self.bookkeeper.new_namespace(trace, current_namespace.id)
    }

    /// Returns a wrapper for BCS proof and first `round_offset` messages are
    /// ignored.
    pub fn from_prover_messages(
        prover_iop_messages_by_round: &'a [SuccinctRoundMessage<F>],
        prover_iop_messages_mt_roots_by_round: &'a [Option<P::InnerDigest>],
        sponge: S,
        ldt_codeword_domain: Option<Radix2CosetDomain<F>>,
        ldt_localization_parameter: Option<usize>,
        trace: TraceInfo,
    ) -> Self {
        let prover_short_messages: Vec<_> = prover_iop_messages_by_round
            .iter()
            .map(|msg| &msg.short_messages)
            .collect();
        let prover_messages_info = prover_iop_messages_by_round
            .iter()
            .map(|msg| msg.get_view().get_info())
            .collect();
        Self {
            prover_short_messages,
            prover_messages_info,
            prover_mt_roots: &prover_iop_messages_mt_roots_by_round,
            sponge,
            current_prover_round: 0,
            bookkeeper: MessageBookkeeper::new(trace),
            reconstructed_verifier_messages: Vec::new(),
            pending_verifier_messages: Vec::new(),
            ldt_codeword_domain,
            ldt_localization_parameter,
            registered_virtual_oracles: Vec::new(),
        }
    }

    /// Returns the number of prover rounds that prover have submitted.
    pub fn num_prover_rounds_submitted(&self) -> usize {
        self.current_prover_round
    }

    /// Receive prover's current round messages, which can possibly contain
    /// multiple oracles with same size. This function will absorb the
    /// merkle tree root and short messages (if any).
    ///
    /// If the function contains low-degree oracle, localization parameter in
    /// `expected_message_info` will be ignored, because localization
    /// parameter is managed by LDT. # Panic
    /// This function will panic is prover message structure contained in proof
    /// is not consistent with `expected_message_structure`.
    pub fn receive_prover_current_round(
        &mut self,
        ns: NameSpace,
        mut expected_message_info: ProverRoundMessageInfo,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        info!("prover round: {}", trace);
        if expected_message_info.reed_solomon_code_degree_bound.len() > 0 {
            // LDT is used, so replace its localization parameter with the one given by LDT
            expected_message_info.localization_parameter = self.ldt_localization_parameter();
        }

        let index = self.current_prover_round;
        self.current_prover_round += 1;

        let trace_info = {
            ark_std::format!(
                "\n Message trace: {}\n Namespace trace: {}",
                trace,
                ns.trace
            )
        };

        if index >= self.prover_messages_info.len() {
            panic!(
                "Verifier tried to receive extra prove round message. {}",
                trace_info
            );
        }

        assert_eq!(
            &expected_message_info, &self.prover_messages_info[index],
            "prover message is not what verifier want at current round. {}",
            trace_info
        );

        // absorb merkle tree root, if any
        self.sponge.absorb(&self.prover_mt_roots[index]);
        // absorb short messages for this round, if any
        self.prover_short_messages[index]
            .iter()
            .for_each(|msg| self.sponge.absorb(msg));
        self.attach_latest_prover_round_to_namespace(ns, false, trace)
    }

    /// Register a virtual oracle specified by coset evaluator.
    pub fn register_prover_virtual_round(
        &mut self,
        ns: NameSpace,
        coset_evaluator: CosetEvaluator<F, SuccinctRoundOracle<'a, F>>,
        test_bound: Vec<usize>,
        constraint_bound: Vec<usize>,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        info!("Register prover virtual oracle: {}", trace);
        // make sure that no virtual oracle is registered when we are halfway sampling
        // verifier round
        assert!(!self.is_pending_message_available());
        let (codeword_domain, localization_param) = (
            self.ldt_codeword_domain(),
            self.ldt_localization_parameter(),
        );
        let virtual_oracle = VirtualOracle::new(
            coset_evaluator,
            codeword_domain,
            localization_param,
            test_bound,
            constraint_bound,
        );

        self.registered_virtual_oracles.push(virtual_oracle);
        self.attach_latest_prover_round_to_namespace(ns, true, trace)
    }

    /// Submit all verifier messages in this round.
    pub fn submit_verifier_current_round(
        &mut self,
        namespace: NameSpace,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        info!("verifier round (sim): {}", trace);
        let pending_message = take(&mut self.pending_verifier_messages);
        self.reconstructed_verifier_messages.push(pending_message);
        self.attach_latest_verifier_round_to_namespace(namespace, trace)
    }

    /// Squeeze sampled verifier message as field elements. The squeezed
    /// elements is attached to pending messages, and need to be submitted
    /// through `submit_verifier_current_round`. Submitted messages will be
    /// stored in transcript and will be later given to verifier in query
    /// and decision phase.
    ///
    /// **Note**: In original IOP paper, verifier do not use sampled element in
    /// commit phase. So in this implementation, this function returns nothing.
    pub fn squeeze_verifier_field_elements(&mut self, field_size: &[FieldElementSize]) {
        let msg = self.sponge.squeeze_field_elements_with_sizes(field_size);
        self.pending_verifier_messages
            .push(VerifierMessage::FieldElements(msg));
    }

    /// Squeeze sampled verifier message as bytes. The squeezed bytes is
    /// attached to pending messages, and need to be submitted through
    /// `submit_verifier_current_round`. Submitted messages will be stored
    /// in transcript and will be later given to verifier in query and
    /// decision phase.
    ///
    /// **Note**: In original IOP paper, verifier do not use sampled element in
    /// commit phase. However, this implementation allows verifier to have
    /// access to sampled elements in `register_iop_structure` to
    /// add flexibility.
    /// User may need to check if this flexibility will affect soundness
    /// analysis in a case-to-case basis.
    pub fn squeeze_verifier_field_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        let msg = self.sponge.squeeze_bytes(num_bytes);
        self.pending_verifier_messages
            .push(VerifierMessage::Bytes(msg.clone()));
        msg
    }

    /// Squeeze sampled verifier message as bytes. The squeezed bytes is
    /// attached to pending messages, and need to be submitted through
    /// `submit_verifier_current_round`. Submitted messages will be stored
    /// in transcript and will be later given to verifier in query and
    /// decision phase.
    ///
    /// **Note**: In original IOP paper, verifier do not use sampled element in
    /// commit phase. However, this implementation allows verifier to have
    /// access to sampled elements in `register_iop_structure` to
    /// add flexibility.
    /// User may need to check if this flexibility will affect soundness
    /// analysis in a case-to-case basis.
    pub fn squeeze_verifier_field_bits(&mut self, num_bits: usize) -> Vec<bool> {
        let msg = self.sponge.squeeze_bits(num_bits);
        self.pending_verifier_messages
            .push(VerifierMessage::Bits(msg.clone()));
        msg
    }

    /// Returns if there is a verifier message for the transcript.
    pub fn is_pending_message_available(&self) -> bool {
        !self.pending_verifier_messages.is_empty()
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
            self.current_prover_round - 1
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
        let index = self.reconstructed_verifier_messages.len() - 1;
        self.bookkeeper
            .attach_verifier_round_to_namespace(namespace, index, trace)
    }
}

impl<'a, P: MTConfig<Leaf = [F]>, S: CryptographicSponge, F: PrimeField + Absorb>
    SimulationTranscript<'a, P, S, F>
where
    P::InnerDigest: Absorb,
{
    /// Return the codeword domain used by LDT.
    ///
    /// **Any low degree oracle will use this domain as evaluation domain.**
    ///
    /// ## Panics
    /// This function panics if LDT is not enabled.
    fn ldt_codeword_domain(&self) -> Radix2CosetDomain<F> {
        self.ldt_codeword_domain.expect("LDT not enabled")
    }

    /// Return the localization parameter used by LDT. Localization parameter is
    /// the size of query coset of the codeword.
    ///
    /// ## Panics
    /// This function panics if LDT is not enabled or localization parameter is
    /// not supported by LDT.
    fn ldt_localization_parameter(&self) -> usize {
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
    fn ldt_codeword_domain(&self) -> Radix2CosetDomain<F>;

    /// Return the localization parameter used by LDT. Localization parameter is
    /// the size of query coset of the codeword.
    ///
    /// ## Panics
    /// This function panics if LDT is not enabled or localization parameter is
    /// not supported by LDT.
    fn ldt_localization_parameter(&self) -> usize;

    /// Given the coset index, return the corresponding query coset of the LDT.
    ///
    /// For example, if the codeword domain is `{a,b,c,d,e,f,g,h}`, and
    /// localization parameter is 2, then this function returns `{a,e}` if the
    /// coset index is 0, `{b,f}` if the coset index is 1, and `{c,g}` if the
    /// coset index is 2, and `{d,h}` if the coset index is 3.
    fn ldt_codeword_query_coset(&self, coset_index: usize) -> Radix2CosetDomain<F> {
        let (codeword_domain, localization_param) = (
            self.ldt_codeword_domain(),
            self.ldt_localization_parameter(),
        );
        codeword_domain
            .query_position_to_coset(coset_index, localization_param)
            .1
    }
}

#[cfg(any(feature = "test_utils", test))]
/// Utilities for testing if `register_iop_structure` is correct
pub mod test_utils {
    use crate::{
        bcs::{
            transcript::{NameSpace, SimulationTranscript, Transcript},
            MTHashParameters,
        },
        iop::{prover::IOPProverWithNoOracleRefs, verifier::IOPVerifierForProver, ProverParam},
        ldt::LDT,
    };
    use ark_crypto_primitives::merkle_tree::Config as MTConfig;
    use ark_ff::PrimeField;
    use ark_sponge::{Absorb, CryptographicSponge};
    use ark_std::collections::BTreeSet;

    /// Check if simulation transcript filled by the verifier is consistent with
    /// prover transcript
    pub fn check_transcript_consistency<P, S, F>(
        prover_transcript: &Transcript<P, S, F>,
        verifier_transcript: &SimulationTranscript<P, S, F>,
    ) where
        P: MTConfig<Leaf = [F]>,
        S: CryptographicSponge,
        F: PrimeField + Absorb,
        P::InnerDigest: Absorb,
    {
        // check namespace consistency
        assert_eq!(
            verifier_transcript
                .bookkeeper
                .messages_store
                .keys()
                .collect::<BTreeSet<_>>(),
            prover_transcript
                .bookkeeper
                .messages_store
                .keys()
                .collect::<BTreeSet<_>>(),
            "inconsistent namespace used"
        );
        // check for each namespace
        verifier_transcript
            .bookkeeper
            .messages_store
            .keys()
            .for_each(|key| {
                let namespace_diag = ark_std::format!(
                    "Prover transcript defines this namespace as {}\n\
             Verifier defines this namespace as {}\n",
                    prover_transcript
                        .bookkeeper
                        .ns_details
                        .get(key)
                        .unwrap()
                        .trace,
                    verifier_transcript
                        .bookkeeper
                        .ns_details
                        .get(key)
                        .unwrap()
                        .trace
                );
                let indices_in_current_namespace_pt =
                    &prover_transcript.bookkeeper.messages_store[key];
                let indices_in_current_namespace_vt =
                    &verifier_transcript.bookkeeper.messages_store[key];

                // prover message should already be verified during prover submit round
                // check verifier message
                (0..indices_in_current_namespace_pt.verifier_messages.len()).for_each(|i| {
                    let verifier_message_trace_pt =
                        &indices_in_current_namespace_pt.verifier_messages[i].trace;
                    let verifier_message_trace_vt =
                        &indices_in_current_namespace_vt.verifier_messages[i].trace;
                    // verifier message gained by prover transcript
                    let verifier_message_pt = &prover_transcript.verifier_messages
                        [indices_in_current_namespace_pt.verifier_messages[i].index];
                    // verifier message gained by verifier simulation transcript
                    let verifier_message_vt = &verifier_transcript.reconstructed_verifier_messages
                        [indices_in_current_namespace_vt.verifier_messages[i].index];

                    assert_eq!(
                        verifier_message_pt, verifier_message_vt,
                        "Inconsistent verifier round #{}.\n\
             Prover transcript message trace: {}\n\
             Verifier transcript message trace: {}\n\
             {}
             ",
                        i, verifier_message_trace_pt, verifier_message_trace_vt, namespace_diag
                    );
                });
            });

        // check sponge final state
        let mut sponge_pt = prover_transcript.sponge.clone();
        let mut sponge_vt = verifier_transcript.sponge.clone();
        // try squeeze something, and check if they are the same
        {
            let a = sponge_pt.squeeze_field_elements::<F>(4);
            let b = sponge_vt.squeeze_field_elements::<F>(4);
            if a != b {
                panic!("Inconsistent sponge state at end of commit phase. ")
            }
        }
    }

    /// Check if verifier's `register_iop_structure` is consistent with
    /// prover's code For now this method only supports protocols that can
    /// start with empty transcript. To unit test subprotocol with oracle
    /// references, you need to write a wrapper.
    ///
    /// Due to current limitation, `check_commit_phase_correctness` cannot check
    /// virtual oracle.
    pub fn check_commit_phase_correctness<
        F: PrimeField + Absorb,
        S: CryptographicSponge,
        MT: MTConfig<Leaf = [F]>,
        P: IOPProverWithNoOracleRefs<F>,
        V: IOPVerifierForProver<S, F, P>,
        L: LDT<F>,
    >(
        sponge: S,
        public_input: &P::PublicInput,
        private_input: &P::PrivateInput,
        prover_parameter: &P::ProverParameter,
        ldt_params: &L::LDTParameters,
        hash_params: MTHashParameters<MT>,
    ) where
        MT::InnerDigest: Absorb,
    {
        // generate transcript using prover perspective
        let transcript_pt = {
            let mut transcript = Transcript::new(
                sponge.clone(),
                hash_params,
                L::codeword_domain(ldt_params),
                L::localization_param(ldt_params),
                iop_trace!("Check commit phase correctness"),
            );
            P::prove(
                NameSpace::root(iop_trace!("check commit phase correctness")),
                &(),
                public_input,
                private_input,
                &mut transcript,
                prover_parameter,
            )
            .unwrap();
            transcript
        };

        // generate transcript using verifier perspective
        let succinct_prover_messages = transcript_pt.all_succinct_messages();
        let prover_mt_roots = transcript_pt.merkle_tree_roots();
        let sponge_vt = sponge.clone();
        let mut transcript_vt = SimulationTranscript::from_prover_messages(
            &succinct_prover_messages,
            &prover_mt_roots,
            sponge_vt,
            L::codeword_domain(ldt_params),
            L::localization_param(ldt_params),
            iop_trace!("check commit phase correctness"),
        );
        V::register_iop_structure(
            NameSpace::root(iop_trace!("check commit phase correctness")),
            &mut transcript_vt,
            &prover_parameter.to_verifier_param(),
        );
        check_transcript_consistency(&transcript_pt, &transcript_vt);
    }
}
