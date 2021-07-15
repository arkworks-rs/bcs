use crate::iop::{
    EncodedProverMessage, IOPProverMessage, IOPVerifierMessage, MTParameters, MessageTree,
    SubprotocolMessage,
};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::borrow::Borrow;
use ark_std::marker::PhantomData;

/// `Transcript` serves as a communication protocol for **prover** to interact with verifier during commit phase..
/// User do not need to implement `Transcript` by themselves. There are two implementations in the crate:
/// * `BCSTranscript`: transcript used for BCS
/// * `SubprotocolTranscript`: a wrapper transcript used for subprotocol.
///
/// `Transcript` stores the prover message, feeds merkle tree root of that message to sponge, and samples verifier message from sponge.
///
/// `P` is the merkle tree config, and `S` is the random oracle that transcript uses.
pub trait Transcript<P: MTConfig, S: CryptographicSponge>: Sized
where
    P::InnerDigest: Absorb,
{
    /// Type of leaf used for merkle tree.
    type Leaf: Borrow<P::Leaf>;
    /// Type of public coin verifier message that can be squeezed from sponge.
    type VerifierMessage: IOPVerifierMessage<S>;
    /// The state of the transcript without sponge. `Self` can be recovered from
    /// `StateWithoutSponge` and a correct sponge state.
    type StateWithoutSponge;

    /// Send prover message to the protocol. Do not send subprotocol message using this method.
    fn send_prover_message(
        &mut self,
        msg: impl IOPProverMessage<P, Leaf = Self::Leaf>,
        mt_params: &MTParameters<P>,
    ) -> Result<(), Error>;

    /// Send verifier message to the protocol. Do not squeeze subprotocl message using this method.
    fn squeeze_verifier_message(&mut self) -> Result<Self::VerifierMessage, Error>;

    /// Convert current transcript to subprotocol transcript with a possibly different
    /// verifier message type.
    fn into_subprotocol<VM>(
        self,
        subprotocol_id: usize,
    ) -> SubprotocolTranscript<P, S, Self, VM>
    where
        VM: IOPVerifierMessage<S> + SubprotocolMessage<Self::VerifierMessage, S>;

    /// Convert current transcript back from subprotocol transcript with a possibly different verifier
    /// message type.
    fn recover_from_subprotocol<VM>(subprotocol: SubprotocolTranscript<P, S, Self, VM>) -> Self
        where
            VM: IOPVerifierMessage<S> + SubprotocolMessage<Self::VerifierMessage, S>;
}

/// SubprotocolTranscript stores the message for subprotocol. When the subprotocol ends,
/// the message will be pushed back to parent protocol.
/// * `MT`: Merkle Tree config used by subprotocol transcript.
/// * `S`: Random oracle used by subprotocol transcript.
/// * `Parent`: Parent transcript.
/// * `VM`: Verifier Message used by this subprotocol transcript.
pub struct SubprotocolTranscript<MT, S, Parent, VM>
where
    MT: MTConfig,
    S: CryptographicSponge,
    Parent: Transcript<MT, S>,
    VM: IOPVerifierMessage<S> + SubprotocolMessage<Parent::VerifierMessage, S>,
    MT::InnerDigest: Absorb,
{
    pub(crate) parent_state: Parent::StateWithoutSponge,
    /// Subprotocol ID of `self`.
    pub(crate) id: usize,
    pub(crate) verifier_messages: MessageTree<Parent::VerifierMessage>,
    pub(crate) encoded_prover_messages: MessageTree<EncodedProverMessage<MT, Parent::Leaf>>,
    pub(crate) sponge_from_parent: S,
    _current_round_vm: PhantomData<VM>,
}

impl<MT, S, Parent, VM> SubprotocolTranscript<MT, S, Parent, VM>
where
    MT: MTConfig,
    S: CryptographicSponge,
    Parent: Transcript<MT, S>,
    VM: IOPVerifierMessage<S> + SubprotocolMessage<Parent::VerifierMessage, S>,
    MT::InnerDigest: Absorb,
{
    /// Create a new subprotocol transcript
    pub fn new(
        subprotocol_id: usize,
        parent_state: Parent::StateWithoutSponge,
        sponge_from_parent: S,
    ) -> Self {
        SubprotocolTranscript {
            parent_state,
            id: subprotocol_id,
            verifier_messages: MessageTree::new(),
            encoded_prover_messages: MessageTree::new(),
            sponge_from_parent,
            _current_round_vm: PhantomData,
        }
    }
}

impl<MT, S, Parent, VM> Transcript<MT, S> for SubprotocolTranscript<MT, S, Parent, VM>
where
    MT: MTConfig,
    S: CryptographicSponge,
    Parent: Transcript<MT, S>,
    VM: IOPVerifierMessage<S> + SubprotocolMessage<Parent::VerifierMessage, S>,
    MT::InnerDigest: Absorb,
{
    type Leaf = Parent::Leaf;
    type VerifierMessage = VM;
    type StateWithoutSponge = (
        Parent::StateWithoutSponge,
        usize,
        MessageTree<Parent::VerifierMessage>,
        MessageTree<EncodedProverMessage<MT, Parent::Leaf>>,
    );

    fn send_prover_message(
        &mut self,
        msg: impl IOPProverMessage<MT, Leaf = Self::Leaf>,
        mt_params: &MTParameters<MT>,
    ) -> Result<(), Error> {
        // encode the message
        let encoded = msg.encode(mt_params)?;
        // calculate the mt root
        let mt_root = encoded.merkle_tree.root();
        // absorb the mt root
        self.sponge_from_parent.absorb(&mt_root);
        // store the encoded prover message for generating proof
        self.encoded_prover_messages
            .push_current_protocol_message(encoded);

        Ok(())
    }

    fn squeeze_verifier_message(&mut self) -> Result<Self::VerifierMessage, Error> {
        let vm = Self::VerifierMessage::from_sponge(&mut self.sponge_from_parent);
        // wrap the message
        let vm_wrapped = vm.to_parent_message();
        // store the verifier message for later decision phase
        self.verifier_messages
            .push_current_protocol_message(vm_wrapped);
        Ok(vm)
    }

    fn into_subprotocol<V>(self, subprotocol_id: usize) -> SubprotocolTranscript<MT, S, Self, V>
    where
        V: IOPVerifierMessage<S> + SubprotocolMessage<Self::VerifierMessage, S>,
    {
        // extract sponge
        let sponge = self.sponge_from_parent;
        // extract state
        let state_without_sponge = (
            self.parent_state,
            self.id,
            self.verifier_messages,
            self.encoded_prover_messages,
        );
        SubprotocolTranscript::new(subprotocol_id, state_without_sponge, sponge)
    }

    fn recover_from_subprotocol<V>(subprotocol: SubprotocolTranscript<MT, S, Self, V>) -> Self
        where
            V: IOPVerifierMessage<S> + SubprotocolMessage<Self::VerifierMessage, S>{
        let sponge = subprotocol.sponge_from_parent;
        let (parent_state, id, verifier_messages, prover_messages) = subprotocol.parent_state;
        let mut transcript = Self {
            parent_state,
            id,
            verifier_messages,
            encoded_prover_messages: prover_messages,
            sponge_from_parent: sponge,
            _current_round_vm: PhantomData,
        };
        // append subprotocol message
        transcript
            .encoded_prover_messages
            .receive_subprotocol_messages(subprotocol.id, subprotocol.encoded_prover_messages);
        // wrap subprotocol message to parent message
        let subprotocol_vm_wrapped = MessageTree::from_subprotocol_message(subprotocol.verifier_messages);
        transcript
            .verifier_messages
            .receive_subprotocol_messages(subprotocol.id, subprotocol_vm_wrapped);
        transcript
    }
}
