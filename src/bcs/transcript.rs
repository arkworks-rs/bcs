use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};

use crate::bcs::message::{RecordingRoundOracle, VerifierMessage, ProverRoundMessageInfo, RoundOracle};
use crate::bcs::MTHashParameters;
use crate::Error;
use ark_crypto_primitives::MerkleTree;
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::univariate::DensePolynomial;
use ark_poly::Polynomial;
use ark_std::collections::BTreeMap;
use ark_std::mem::take;
use crate::bcs::prover::BCSProof;

/// # Namespace
/// The namespace is an Each protocol is a list of subprotocol_id that represents a path.
/// Subprotocol ID should be unique in scope of current running protocol, but do not need to be unique
/// in scope of all protocols used. For example, if a subprotocol uses a subprotocol that has id `3`,
/// it is fine to use `3` for current protocol.
///
/// Each protocol should have a unique namespace,
/// and should only send prover message and receive verifier message use its own namespace.
pub type NameSpace = Vec<u32>;
/// Given current namespace, create a namespace for subprotocol.
pub fn create_subprotocol_namespace(
    current_namespace: &NameSpace,
    subprotocol_id: u32,
) -> NameSpace {
    let mut result = (*current_namespace).clone();
    result.push(subprotocol_id);
    result
}

#[derive(Clone, Default, Eq, PartialEq, Debug)]
/// Stores the ownership relation of each message to its protocol.
pub struct MessageBookkeeper {
    /// TODO doc
    pub map: BTreeMap<NameSpace, MessageIndices>,
}

/// Namespace `/`
pub const ROOT_NAMESPACE: NameSpace = NameSpace::new();

impl MessageBookkeeper {
    pub fn new_namespace(&mut self, namespace: NameSpace) {
        if self.map.contains_key(&namespace) {
            panic!("namespace already exists")
        };
        self.map.insert(
            namespace.clone(),
            MessageIndices {
                prover_message_locations: Vec::new(),
                verifier_message_locations: Vec::new(),
            },
        );
    }

    /// Return the mutable message indices for current namespace.
    pub fn fetch_node_mut(&mut self, namespace: &NameSpace) -> Option<&mut MessageIndices> {
        self.map.get_mut(namespace)
    }

    /// Does namespace exist in bookkeeper?
    pub fn is_namespace_exist(&self, namespace: &NameSpace) -> bool {
        self.map.contains_key(namespace)
    }

    /// Return the message indices for current namespace.
    pub fn get_message_indices(&self, namespace: &NameSpace) -> &MessageIndices {
        self.map.get(namespace).expect("message indices not exist")
    }

    /// Get verifier messages in this namespace.
    /// If bookkeeper points to some invalid message locations, return None.
    pub fn get_verifier_messages_in_namespace<'a, T: 'a>(
        &self,
        namespace: &NameSpace,
        verifier_messages: &'a [T],
    ) -> Option<Vec<&'a T>> {
        let indices = self.get_message_indices(namespace);
        let messages: Option<Vec<_>> = indices
            .verifier_message_locations
            .iter()
            .map(|&x| verifier_messages.get(x))
            .collect();
        messages
    }

    /// Get prover message oracles in this namespace.
    /// If bookkeeper points to some invalid message locations, return None.
    pub fn get_prover_message_oracles_in_namespace<'a, T: 'a>(
        &self,
        namespace: &NameSpace,
        prover_messages: &'a [T],
    ) -> Option<Vec<&'a T>> {
        let indices = self.get_message_indices(namespace);
        let messages: Option<Vec<_>> = indices
            .prover_message_locations
            .iter()
            .map(|&x| prover_messages.get(x))
            .collect();
        messages
    }
}

/// contains indices of current protocol messages.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct MessageIndices {
    pub prover_message_locations: Vec<usize>,
    pub verifier_message_locations: Vec<usize>,
}

#[derive(Clone)]
#[allow(variant_size_differences)]
/// Pending message for current transcript. We allow `variant_size_differences` here because there will
/// only be one `PendingMessage` per transcript.
enum PendingMessage<F: PrimeField + Absorb> {
    ProverMessage(RecordingRoundOracle<F>),
    VerifierMessage(Vec<VerifierMessage<F>>),
    None,
}

impl<F: PrimeField + Absorb> Default for PendingMessage<F> {
    fn default() -> Self {
        Self::None
    }
}

/// A communication protocol for IOP prover.
#[derive(Clone)]
pub struct Transcript<P: MTConfig, S: CryptographicSponge, F: PrimeField + Absorb>
where
    P::InnerDigest: Absorb,
{
    /// merkle tree hash parameters
    pub hash_params: MTHashParameters<P>,
    /// Messages sent by prover in commit phase. Each item in the vector represents a list of
    /// message oracles with same length. The length constraints do not hold for short messages (IP message).
    /// All non-IP messages in the same prover round should share the same merkle tree. Each merkle tree leaf is
    /// a vector which each element correspond to the same location of different oracles
    pub prover_message_oracles: Vec<RecordingRoundOracle<F>>,
    /// Each element `merkle_tree_for_each_round[i]` corresponds to the merkle tree for `prover_message_oracles[i]`. If no oracle
    /// messages in this round, merkle tree will be `None`.
    pub merkle_tree_for_each_round: Vec<Option<MerkleTree<P>>>,
    /// Sampled Message sent by verifier in commit phase. In each round, verifier can send multiple messages.
    pub verifier_messages: Vec<Vec<VerifierMessage<F>>>,
    /// bookkeepers for messages in different subprotocols
    pub bookkeeper: MessageBookkeeper,
    /// Random Oracle to sample verifier messages.
    pub sponge: S,
    pending_message_for_current_round: PendingMessage<F>,
}

impl<P, S, F> Transcript<P, S, F>
where
    P: MTConfig<Leaf = Vec<F>>,
    S: CryptographicSponge,
    F: PrimeField + Absorb,
    P::InnerDigest: Absorb,
{
    /// Return a new BCS transcript.
    pub fn new(sponge: S, hash_params: MTHashParameters<P>) -> Self {
        Self {
            prover_message_oracles: Vec::new(),
            merkle_tree_for_each_round: Vec::new(),
            verifier_messages: Vec::new(),
            bookkeeper: MessageBookkeeper {
                map: BTreeMap::new(),
            },
            sponge,
            hash_params,
            pending_message_for_current_round: PendingMessage::default(),
        }
    }

    pub fn new_namespace(&mut self, id: NameSpace) {
        self.bookkeeper.new_namespace(id)
    }

    /// Submit all prover oracles in this round, and set pending round message to `None`
    /// # Panic
    /// Panic if current prover round messages is `None` or `VerifierMessage`
    pub fn submit_prover_current_round(&mut self, namespace: &NameSpace) -> Result<(), Error> {
        let pending_message = take(&mut self.pending_message_for_current_round);
        if let PendingMessage::ProverMessage(round_msg) = pending_message {
            // generate merkle tree
            let mt = round_msg.generate_merkle_tree(&self.hash_params)?;
            // if this round prover message contains oracle messages, absorb merkle tree root
            self.sponge.absorb(&mt.as_ref().map(|x| x.root()));
            // if this round prover message has non-oracle messages, absorb them in entirety
            round_msg
                .short_messages
                .iter()
                .for_each(|msg| self.sponge.absorb(msg));
            self.prover_message_oracles.push(round_msg);
            self.merkle_tree_for_each_round.push(mt);
            self.attach_latest_prover_round_to_namespace(namespace);
            Ok(())
        } else {
            panic!("Current pending message is not prover message!")
        }
    }

    /// Submit all verifier messages in this round, and set pending round message to `None`.
    /// # Panic
    /// Panic if current verifier round messages is `None` or `ProverMessage`
    pub fn submit_verifier_current_round(&mut self, namespace: &NameSpace) {
        let pending_message = take(&mut self.pending_message_for_current_round);
        if let PendingMessage::VerifierMessage(round_msg) = pending_message {
            self.verifier_messages.push(round_msg);
            self.attach_latest_verifier_round_to_namespace(namespace);
        } else {
            panic!("Current pending message is not prover message!")
        }
    }

    /// Send univariate polynomial with LDT.
    /// `domain` should be consistent with LDT that user provides.
    /// TODO: check domain during BCS prove.
    pub fn send_univariate_polynomial(
        &mut self,
        degree_bound: usize,
        poly: &DensePolynomial<F>,
        domain: Radix2CosetDomain<F>,
    ) -> Result<(), Error> {
        // check degree bound
        if poly.degree() > degree_bound {
            panic!("polynomial degree is greater than degree bound!");
        }
        // evaluate the poly using ldt domain
        let evaluations = domain.evaluate(poly);
        self.send_oracle_evaluations_unchecked(evaluations, degree_bound)?;
        Ok(())
    }

    /// Send Reed-Solomon codes of a polynomial.
    /// Domain should be consistent with LDT that user provides.
    /// todo: remove LDT, and check domain afterwards
    pub fn send_oracle_evaluations(
        &mut self,
        msg: impl IntoIterator<Item = F>,
        degree_bound: usize,
    ) -> Result<(), Error> {
        self.send_oracle_evaluations_unchecked(msg, degree_bound)?;
        Ok(())
    }

    fn send_oracle_evaluations_unchecked(
        &mut self,
        msg: impl IntoIterator<Item = F>,
        degree_bound: usize,
    ) -> Result<(), Error> {
        // encode the message
        let oracle = msg.into_iter().collect();
        self.current_prover_pending_message()
            .reed_solomon_codes
            .push((oracle, degree_bound));
        Ok(())
    }

    /// Send prover message oracles.
    /// Note that transcript will not do low-degree test on this oracle.
    /// Returns the index of message.
    pub fn send_message_oracle(&mut self, msg: impl IntoIterator<Item = F>) -> Result<(), Error> {
        // encode the message
        let oracle = msg.into_iter().collect();
        // store the encoded prover message for generating proof
        self.current_prover_pending_message()
            .message_oracles
            .push(oracle);

        Ok(())
    }

    /// Send short message that does not need to be an oracle. The entire message will be included
    /// in BCS proof, and no merkle tree will be generated.
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

    /// Squeeze sampled verifier message as field elements. The squeezed elements is attached to
    /// pending messages, and need to be submitted through `submit_verifier_current_round`.
    /// Submitted messages will be stored in transcript and will be later
    /// given to verifier in query and decision phase.
    pub fn squeeze_verifier_field_elements(&mut self, field_size: &[FieldElementSize]) -> Vec<F> {
        // squeeze message
        let msg = self.sponge.squeeze_field_elements_with_sizes(field_size);
        // store the verifier message for later decision phase
        self.current_verifier_pending_message()
            .push(VerifierMessage::FieldElements(msg.clone()));
        msg
    }

    /// Squeeze sampled verifier message as bytes. The squeezed elements is attached to pending messages,
    /// and need to be submitted through `submit_verifier_current_round`. Submitted messages will be stored in transcript
    /// and will be later given to verifier in query and decision phase.
    pub fn squeeze_verifier_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        // squeeze message
        let msg = self.sponge.squeeze_bytes(num_bytes);
        // store the verifier message for later decision phase
        self.current_verifier_pending_message()
            .push(VerifierMessage::Bytes(msg.clone()));
        msg
    }

    /// Squeeze sampled verifier message as bits. The squeezed elements is attached to pending messages,
    /// and need to be submitted through `submit_verifier_current_round`. Submitted messages will be stored in transcript
    /// and will be later given to verifier in query and decision phase.
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

    /// Get reference to current prover pending message.
    /// If current round pending message to `None`, current round message will become prover message type.
    /// Panic if current pending message is not prover message.
    fn current_prover_pending_message(
        &mut self,
    ) -> &mut RecordingRoundOracle<F> {
        if let PendingMessage::None = &self.pending_message_for_current_round {
            self.pending_message_for_current_round =
                PendingMessage::ProverMessage(RecordingRoundOracle::default());
        }
        match &mut self.pending_message_for_current_round {
            PendingMessage::ProverMessage(msg) => msg,
            PendingMessage::VerifierMessage(_) => panic!("Pending message is verifier message"),
            _ => unreachable!(),
        }
    }

    /// Get reference to current verifier pending message.
    /// If current round pending message to `None`, current round message will become verifier message type.
    /// Panic if current pending message is not verifier message.
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

    fn attach_latest_prover_round_to_namespace(&mut self, namespace: &NameSpace) {
        // add verifier message index to namespace
        let index = self.prover_message_oracles.len() - 1;
        self.bookkeeper
            .fetch_node_mut(namespace)
            .expect("namespace not found")
            .prover_message_locations
            .push(index);
    }

    fn attach_latest_verifier_round_to_namespace(&mut self, namespace: &NameSpace) {
        // add verifier message index to namespace
        let index = self.verifier_messages.len() - 1;
        self.bookkeeper
            .fetch_node_mut(namespace)
            .expect("namespace not found")
            .verifier_message_locations
            .push(index);
    }
}

/// A wrapper for BCS proof, so that verifier can reconstruct verifier messages by simulating commit phase
/// easily.
pub struct SimulationTranscript<'a, P: MTConfig, S: CryptographicSponge, F: PrimeField + Absorb>
    where
        P::InnerDigest: Absorb,
{
    /// prover message info used to verify consistency
    prover_messages_info: Vec<ProverRoundMessageInfo>,

    /// For each round submit, absorb merkle tree root first
    prover_mt_roots: &'a [Option<P::InnerDigest>],
    /// After absorb merkle tree root for this round, absorb the short messages in entirety
    prover_short_messages: Vec<&'a Vec<Vec<F>>>,

    /// sponge is used to sample verifier message
    sponge: &'a mut S,
    /// the next prover round message to absorb
    pub(crate) current_prover_round: usize,

    /// Those reconstructed messages will be used in query and decision phase
    pub(crate) reconstructed_verifer_messages: Vec<Vec<VerifierMessage<F>>>,

    pending_verifier_messages: Vec<VerifierMessage<F>>,
    pub(crate) bookkeeper: MessageBookkeeper,
}

impl<'a, P: MTConfig, S: CryptographicSponge, F: PrimeField + Absorb>
    SimulationTranscript<'a, P, S, F>
where
    P::InnerDigest: Absorb,
{
    /// Returns a wrapper for BCS proof so that verifier can reconstruct verifier messages by simulating commit phase easily.
    pub(crate) fn new_main_transcript(bcs_proof: &'a BCSProof<P, F>, sponge: &'a mut S) -> Self {
        let prover_short_messages: Vec<_> = bcs_proof
            .prover_messages
            .iter()
            .map(|msg| &msg.short_messages)
            .collect();
        let prover_messages_info: Vec<_> = bcs_proof
            .prover_messages
            .iter()
            .map(|msg| msg.get_view().get_info())
            .collect();
        Self {
            prover_short_messages,
            prover_messages_info,
            prover_mt_roots: &bcs_proof.prover_messages_mt_root,
            sponge,
            current_prover_round: 0,
            bookkeeper: MessageBookkeeper::default(),
            reconstructed_verifer_messages: Vec::new(),
            pending_verifier_messages: Vec::new(),
        }
    }

    /// Returns a wrapper for BCS proof so that LDT verifier can reconstruct verifier messages by simulating commit phase easily.
    pub(crate) fn new_ldt_transcript(bcs_proof: &'a BCSProof<P, F>, sponge: &'a mut S) -> Self {
        let prover_short_messages: Vec<_> = bcs_proof
            .ldt_prover_messages
            .iter()
            .map(|msg| &msg.short_messages)
            .collect();
        let prover_messages_info = bcs_proof
            .ldt_prover_messages
            .iter()
            .map(|msg| msg.get_view().get_info())
            .collect();
        Self {
            prover_short_messages,
            prover_messages_info,
            prover_mt_roots: &bcs_proof.ldt_prover_messages_mt_root,
            sponge,
            current_prover_round: 0,
            bookkeeper: MessageBookkeeper::default(),
            reconstructed_verifer_messages: Vec::new(),
            pending_verifier_messages: Vec::new(),
        }
    }

    /// Receive prover's current round messages, which can possibly contain multiple oracles with same size.
    /// This function will absorb the merkle tree root and short messages (if any).
    /// # Panic
    /// This function will panic is prover message structure contained in proof is not consistent with `expected_message_structure`.
    pub fn receive_prover_current_round(
        &mut self,
        ns: &NameSpace,
        expected_message_info: &ProverRoundMessageInfo,
    ) {
        let index = self.current_prover_round;
        self.current_prover_round += 1;

        assert_eq!(
            expected_message_info, &self.prover_messages_info[index],
            "prover message is not what verifier want at current round"
        );

        // absorb merkle tree root, if any
        self.sponge.absorb(&self.prover_mt_roots[index]);
        // absorb short messages for this round, if any
        self.prover_short_messages[index]
            .iter()
            .for_each(|msg| self.sponge.absorb(msg));
        self.attach_latest_prover_round_to_namespace(ns);
    }

    /// Submit all verifier messages in this round.
    pub fn submit_verifier_current_round(&mut self, namespace: &NameSpace) {
        let pending_message = take(&mut self.pending_verifier_messages);
        self.reconstructed_verifer_messages.push(pending_message);
        self.attach_latest_verifier_round_to_namespace(namespace);
    }

    /// Squeeze sampled verifier message as field elements. The squeezed elements is attached to
    /// pending messages, and need to be submitted through `submit_verifier_current_round`.
    /// Submitted messages will be stored in transcript and will be later
    /// given to verifier in query and decision phase.
    ///
    /// **Note**: Since we are not running the actual prover code, verifier message is not used
    /// `reconstructed_verifer_messages`, so this function returns nothing.
    pub fn squeeze_verifier_field_elements(&mut self, field_size: &[FieldElementSize]) {
        let msg = self.sponge.squeeze_field_elements_with_sizes(field_size);
        self.pending_verifier_messages
            .push(VerifierMessage::FieldElements(msg));
    }

    /// Squeeze sampled verifier message as bytes. The squeezed bytes is attached to
    /// pending messages, and need to be submitted through `submit_verifier_current_round`.
    /// Submitted messages will be stored in transcript and will be later
    /// given to verifier in query and decision phase.
    ///
    /// **Note**: Since we are not running the actual prover code, verifier message is not used
    /// `reconstructed_verifer_messages`, so this function returns nothing.
    pub fn squeeze_verifier_field_bytes(&mut self, num_bytes: usize) {
        let msg = self.sponge.squeeze_bytes(num_bytes);
        self.pending_verifier_messages
            .push(VerifierMessage::Bytes(msg));
    }

    /// Squeeze sampled verifier message as bytes. The squeezed bytes is attached to
    /// pending messages, and need to be submitted through `submit_verifier_current_round`.
    /// Submitted messages will be stored in transcript and will be later
    /// given to verifier in query and decision phase.
    ///
    /// **Note**: Since we are not running the actual prover code, verifier message is not used
    /// `reconstructed_verifer_messages`, so this function returns nothing.
    pub fn squeeze_verifier_field_bits(&mut self, num_bits: usize) {
        let msg = self.sponge.squeeze_bits(num_bits);
        self.pending_verifier_messages
            .push(VerifierMessage::Bits(msg));
    }

    /// Returns if there is a verifier message for the transcript.
    pub fn is_pending_message_available(&self) -> bool {
        !self.pending_verifier_messages.is_empty()
    }

    fn attach_latest_prover_round_to_namespace(&mut self, namespace: &NameSpace) {
        // add verifier message index to namespace
        let index = self.current_prover_round - 1;
        self.bookkeeper
            .fetch_node_mut(namespace)
            .expect("namespace not found")
            .prover_message_locations
            .push(index);
    }

    fn attach_latest_verifier_round_to_namespace(&mut self, namespace: &NameSpace) {
        // add verifier message index to namespace
        let index = self.reconstructed_verifer_messages.len() - 1;
        self.bookkeeper
            .fetch_node_mut(namespace)
            .expect("namespace not found")
            .verifier_message_locations
            .push(index);
    }

    #[cfg(test)]
    /// test whether `reconstructed_verifer_messages` simulate the prover-verifier interaction in
    /// commit phase correctly.
    pub fn check_correctness(&self, prover_transcript: &Transcript<P, S, F>) {
        // TODO: give information about which namespace is incorrect
        assert_eq!(prover_transcript.bookkeeper,
                   self.bookkeeper,
                   "your simulation code submits incorrect number of rounds, or call subprotocols in incorrect order.");

        // TODO: give information about which message in which namespace is incorrect
        assert_eq!(prover_transcript.verifier_messages,
                   self.reconstructed_verifer_messages,
                   "reconstructed verifer messages is inconsistent with verifier messages sampled in prover code");
    }
}

