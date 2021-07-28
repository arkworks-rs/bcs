use crate::iop::MTHashParameters;

use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};

use crate::bcs::message::{
    MessageOracle, MessageRecordingOracle, ProverMessage, SuccinctOracle, VerifierMessage,
};
use crate::bcs::prover::BCSProof;
use crate::ldt_trait::LDT;
use crate::Error;
use ark_crypto_primitives::MerkleTree;
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::univariate::DensePolynomial;
use ark_poly::Polynomial;
use ark_std::collections::BTreeMap;
use std::marker::PhantomData;

/// # Namespace
/// The namespace is an Each protocol is a linked list of subprotocol_id that represents a path.
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

#[derive(Clone)]
/// Stores the ownership relation of each message to its protocol.
pub struct MessageBookkeeper {
    /// TODO doc
    pub map: BTreeMap<NameSpace, MessageIndices>,
}

/// Namespace `/`
pub const ROOT_NAMESPACE: NameSpace = NameSpace::new();

impl MessageBookkeeper {
    pub fn new_namespace(&mut self, namespace: &NameSpace) {
        if self.map.contains_key(namespace) {
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
#[derive(Clone)]
pub struct MessageIndices {
    pub prover_message_locations: Vec<usize>,
    pub verifier_message_locations: Vec<usize>,
}

/// A communication protocol for IOP prover.
#[derive(Clone)]
pub struct Transcript<P: MTConfig, S: CryptographicSponge, F: PrimeField, L: LDT<P, F, S>> {
    /// merkle tree hash parameters
    pub hash_params: MTHashParameters<P>,
    /// Message sent by prover in commit phase.
    pub prover_message_oracles: Vec<ProverMessage<P, F, MessageRecordingOracle<P, F>>>,
    /// Sampled Message sent by verifier in commit phase.
    pub verifier_messages: Vec<VerifierMessage<F>>,
    /// bookkeepers for messages in different subprotocols
    pub bookkeeper: MessageBookkeeper,
    /// Random Oracle to sample verifier messages.
    pub sponge: S,
    _ldt: PhantomData<L>,
}

/// rename RS-IOP transcript
impl<P, S, F, L> Transcript<P, S, F, L>
where
    P: MTConfig<Leaf = F>,
    S: CryptographicSponge,
    F: PrimeField,
    L: LDT<P, F, S>,
    P::InnerDigest: Absorb,
{
    /// Return a new BCS transcript.
    pub fn new(sponge: S, hash_params: MTHashParameters<P>) -> Self {
        Self {
            prover_message_oracles: Vec::new(),
            verifier_messages: Vec::new(),
            bookkeeper: MessageBookkeeper {
                map: BTreeMap::new(),
            },
            sponge,
            hash_params,
            _ldt: PhantomData,
        }
    }

    pub fn new_namespace(&mut self, id: &NameSpace) {
        self.bookkeeper.new_namespace(id)
    }

    /// Send univariate polynomial with LDT.
    pub fn send_univariate_polynomial(
        &mut self,
        namespace: &NameSpace,
        degree_bound: usize,
        poly: &DensePolynomial<F>,
    ) -> Result<usize, Error> {
        // check degree bound
        if poly.degree() > degree_bound {
            panic!("polynomial degree is greater than degree bound!");
        }
        // evaluate the poly using ldt domain
        let (enforced_bound, domain) = L::ldt_info(degree_bound);
        let evaluations = domain.evaluate(poly);
        self.send_oracle_evaluations_unchecked(namespace, evaluations, degree_bound)?;
        Ok(enforced_bound)
    }

    /// Send Reed-Solomon codes of a polynomial.
    pub fn send_oracle_evaluations(
        &mut self,
        namespace: &NameSpace,
        msg: impl IntoIterator<Item = F>,
        domain: Radix2CosetDomain<F>,
        degree_bound: usize,
    ) -> Result<usize, Error> {
        // check domain validity
        let (enforced_bound, suggested_domain) = L::ldt_info(degree_bound);
        if domain != suggested_domain {
            panic!("invalid domain")
        }

        self.send_oracle_evaluations_unchecked(namespace, msg, degree_bound)?;
        Ok(enforced_bound)
    }

    fn send_oracle_evaluations_unchecked(
        &mut self,
        namespace: &NameSpace,
        msg: impl IntoIterator<Item = F>,
        degree_bound: usize,
    ) -> Result<(), Error> {
        // encode the message
        let encoded = self.encode_message_oracle(msg)?;
        // calculate the mt root
        let mt_root = encoded.merkle_tree.root();
        // absorb the mt root
        self.sponge.absorb(&mt_root);
        // store the encoded prover message for generating proof
        self.prover_message_oracles
            .push(ProverMessage::ReedSolomonCode {
                oracle: encoded,
                degree_bound,
                _mt_config: PhantomData,
            });
        self.attach_latest_prover_message_to_namespace(namespace);
        Ok(())
    }

    /// Send prover message oracles.
    /// Note that transcript will not do low-degree test on this oracle.
    /// Returns the index of message.
    pub fn send_message_oracle(
        &mut self,
        namespace: &NameSpace,
        msg: impl IntoIterator<Item = F>,
    ) -> Result<(), Error> {
        // encode the message
        let encoded = self.encode_message_oracle(msg)?;
        // calculate the mt root
        let mt_root = encoded.merkle_tree.root();
        // absorb the mt root
        self.sponge.absorb(&mt_root);
        // store the encoded prover message for generating proof
        self.prover_message_oracles
            .push(ProverMessage::MessageOracle {
                oracle: encoded,
                _mt_config: PhantomData,
            });
        self.attach_latest_prover_message_to_namespace(namespace);

        Ok(())
    }

    /// Send short message that does not need to be an oracle. The entire message will be included
    /// in BCS proof, and no merkle tree will be generated.
    pub fn send_ip_message(&mut self, namespace: &NameSpace, msg: impl IntoIterator<Item = F>)
    where
        F: Absorb,
    {
        let message: Vec<_> = msg.into_iter().collect();
        // absorb entire message
        self.sponge.absorb(&message);
        // store the message
        self.prover_message_oracles
            .push(ProverMessage::IP { message });
        self.attach_latest_prover_message_to_namespace(namespace);
    }

    fn encode_message_oracle(
        &self,
        msg: impl IntoIterator<Item = F>,
    ) -> Result<MessageRecordingOracle<P, F>, Error> {
        let leaves: Vec<_> = msg.into_iter().collect();
        let merkle_tree = MerkleTree::new(
            &self.hash_params.leaf_hash_param,
            &self.hash_params.inner_hash_param,
            &leaves,
        )?;
        Ok(MessageRecordingOracle {
            leaves,
            merkle_tree,
            query_responses: BTreeMap::new(),
        })
    }

    /// Squeeze sampled verifier message as field elements. The squeezed elements is stored
    /// in transcript and will be later given to verifier in query and decision phase.
    pub fn squeeze_verifier_field_elements(
        &mut self,
        namespace: &NameSpace,
        field_size: &[FieldElementSize],
    ) -> Vec<F> {
        // squeeze message
        let msg = self.sponge.squeeze_field_elements_with_sizes(field_size);
        // store the verifier message for later decision phase
        self.verifier_messages
            .push(VerifierMessage::FieldElements(msg.clone()));
        self.attach_latest_verifier_message_to_namespace(namespace);
        msg
    }

    /// Squeeze sampled verifier message as bytes. The squeezed elements is stored
    /// in transcript and will be later given to verifier in query and decision phase.
    pub fn squeeze_verifier_bytes(&mut self, namespace: &NameSpace, num_bytes: usize) -> Vec<u8> {
        // squeeze message
        let msg = self.sponge.squeeze_bytes(num_bytes);
        // store the verifier message for later decision phase
        self.verifier_messages
            .push(VerifierMessage::Bytes(msg.clone()));
        self.attach_latest_verifier_message_to_namespace(namespace);
        msg
    }

    /// Squeeze sampled verifier message as bits The squeezed elements is stored
    /// in transcript and will be later given to verifier in query and decision phase.
    pub fn squeeze_verifier_bits(&mut self, namespace: &NameSpace, num_bits: usize) -> Vec<bool> {
        // squeeze message
        let msg = self.sponge.squeeze_bits(num_bits);
        // store the verifier message for later decision phase
        self.verifier_messages
            .push(VerifierMessage::Bits(msg.clone()));
        self.attach_latest_verifier_message_to_namespace(namespace);
        msg
    }

    fn attach_latest_prover_message_to_namespace(&mut self, namespace: &NameSpace) {
        // add verifier message index to namespace
        let index = self.prover_message_oracles.len() - 1;
        self.bookkeeper
            .fetch_node_mut(namespace)
            .expect("namespace not found")
            .prover_message_locations
            .push(index);
    }

    fn attach_latest_verifier_message_to_namespace(&mut self, namespace: &NameSpace) {
        // add verifier message index to namespace
        let index = self.verifier_messages.len() - 1;
        self.bookkeeper
            .fetch_node_mut(namespace)
            .expect("namespace not found")
            .verifier_message_locations
            .push(index);
    }
}

/// A communication protocol for IOP verifier, which is used to reconstruct verifier messages.
/// This transcript includes merkle tree roots, which acts as a simulation of prover in commit phase.
pub struct SimulationTranscript<
    'a,
    P: MTConfig,
    S: CryptographicSponge,
    F: PrimeField,
    L: LDT<P, F, S>,
> where
    P::InnerDigest: Absorb,
{
    /// Prover message oracles extracted from proof.
    pub prover_message_oracles: &'a [ProverMessage<P, F, SuccinctOracle<P, F>>],
    /// Sampled message sent by verifier in commit phase.
    /// Generated during prover simulation.
    pub verifier_messages: Vec<VerifierMessage<F>>,
    /// Bookkeeper for messages in different subprotocols.
    /// Generated during prover simulation.
    ///
    /// **Note**: A simple sanity check to make sure prover simulation in `reconstruct_verifier_messages` is consistent with prover
    /// function, is to check if the two bookkeepers are consistent.
    pub bookkeeper: MessageBookkeeper,
    /// random oracle
    pub sponge: S,
    num_prover_messages_sent: usize,
    _ldt: PhantomData<L>,
}

impl<'a, P: MTConfig, S: CryptographicSponge, F: PrimeField, L: LDT<P, F, S>>
    SimulationTranscript<'a, P, S, F, L>
where
    P::InnerDigest: Absorb,
{
    /// Returns a new simulation transcript that can be used to reconstruct verifier message.
    pub fn new(proof: &'a BCSProof<P, F, S, L>, sponge: S) -> Self {
        let prover_message_oracles = proof.prover_message.as_slice();
        let verifier_messages = Vec::new();
        let bookkeeper = MessageBookkeeper {
            map: BTreeMap::new(),
        };
        Self {
            prover_message_oracles,
            verifier_messages,
            bookkeeper,
            sponge,
            num_prover_messages_sent: 0,
            _ldt: PhantomData,
        }
    }

    /// Receive prover's next message as oracle evaluations and absorb merkle tree root to sponge.
    ///
    /// # Panics
    /// This function will panic if prover sends messages of different type or degree bound.
    pub fn receive_oracle_evaluations(
        &mut self,
        namespace: &NameSpace,
        domain: Radix2CosetDomain<F>,
        degree_bound: usize,
    ) -> usize {
        // check domain validity
        let (enforced_bound, suggested_domain) = L::ldt_info(degree_bound);
        if domain != suggested_domain {
            panic!("invalid domain");
        }

        // get the current message oracle
        let current_msg = &self.receive_prover_next_message(namespace);
        // absorb to sponge
        match current_msg {
            ProverMessage::ReedSolomonCode {
                degree_bound: received_degree_bound,
                oracle,
                ..
            } => {
                if degree_bound != *received_degree_bound {
                    panic!(
                        "want to receive a poly with degree bound {}, got degree bound {}",
                        degree_bound, *received_degree_bound
                    )
                }
                let mt_root = oracle.mt_root();
                self.sponge.absorb(&mt_root);
            }
            _ => {
                panic!(
                    "want to receive a poly with degree bound {}, got {}",
                    degree_bound, current_msg
                );
            }
        };

        enforced_bound
    }

    /// Receive prover's next message as message oracle without LDT and absorb merkle tree root to sponge.
    ///
    /// # Panics
    /// This function will panic if prover sends messages of different type or degree bound.
    pub fn receive_message_oracle(&mut self, namespace: &NameSpace) {
        // get the current message oracle
        let current_msg = self.receive_prover_next_message(namespace);
        match current_msg {
            ProverMessage::MessageOracle { oracle, .. } => {
                let mt_root = oracle.mt_root();
                self.sponge.absorb(&mt_root)
            }
            _ => panic!("want to receive a message oracle, got {}", current_msg),
        }
    }

    /// Receive prover's next message as short IP message and absorb entire message to sponge.
    ///
    /// # Panics
    /// This function will panic if prover sends messages of different type or degree bound.
    pub fn receive_ip_message(&mut self, namespace: &NameSpace)
    where
        F: Absorb,
    {
        let current_msg = self.receive_prover_next_message(namespace);
        match current_msg {
            ProverMessage::IP { message } => {
                let msg = message.clone();
                self.sponge.absorb(&msg)
            }
            _ => panic!("want to receive an IP message, got {}", current_msg),
        }
    }

    /// Squeeze sampled verifier message as field elements. The squeezed elements is stored
    /// in simulation transcript and will be later given to verifier in query and decision phase.
    pub fn squeeze_verifier_field_elements(
        &mut self,
        namespace: &NameSpace,
        field_size: &[FieldElementSize],
    ) {
        // squeeze message
        let msg = self.sponge.squeeze_field_elements_with_sizes(field_size);
        // store the verifier message for later decision phase
        self.verifier_messages
            .push(VerifierMessage::FieldElements(msg));
        self.attach_latest_verifier_message_to_namespace(namespace);
    }

    /// Squeeze sampled verifier message as bytes. The squeezed elements is stored
    /// in simulation transcript and will be later given to verifier in query and decision phase.
    pub fn squeeze_verifier_bytes(&mut self, namespace: &NameSpace, num_bytes: usize) {
        // squeeze message
        let msg = self.sponge.squeeze_bytes(num_bytes);
        // store the verifier message for later decision phase
        self.verifier_messages.push(VerifierMessage::Bytes(msg));
        self.attach_latest_verifier_message_to_namespace(namespace);
    }

    /// Squeeze sampled verifier message as bits. The squeezed elements is stored
    /// in simulation transcript and will be later given to verifier in query and decision phase.
    pub fn squeeze_verifier_bits(&mut self, namespace: &NameSpace, num_bits: usize) {
        // squeeze message
        let msg = self.sponge.squeeze_bits(num_bits);
        // store the verifier message for later decision phase
        self.verifier_messages.push(VerifierMessage::Bits(msg));
        self.attach_latest_verifier_message_to_namespace(namespace);
    }

    /// Receive prover next message oracle from proof.
    /// This function increment the prover message counter by 1, add current prover message to namespace,
    /// but does not absorb message to sponge.
    ///
    /// This function does not absorb
    fn receive_prover_next_message(
        &mut self,
        namespace: &NameSpace,
    ) -> &ProverMessage<P, F, SuccinctOracle<P, F>> {
        // get the current message oracle
        let current_msg = &self.prover_message_oracles[self.num_prover_messages_sent];
        self.num_prover_messages_sent += 1;
        // add message to namespace and get message index in namespace
        self.attach_latest_prover_message_to_namespace(namespace);
        current_msg
    }

    /// returns the index of current message in namespace
    fn attach_latest_prover_message_to_namespace(&mut self, namespace: &NameSpace) {
        self.bookkeeper
            .fetch_node_mut(namespace)
            .expect("namespace not found")
            .prover_message_locations
            .push(self.num_prover_messages_sent - 1);
    }

    fn attach_latest_verifier_message_to_namespace(&mut self, namespace: &NameSpace) {
        self.bookkeeper
            .fetch_node_mut(namespace)
            .expect("namespace not found")
            .verifier_message_locations
            .push(self.verifier_messages.len() - 1);
    }
}
