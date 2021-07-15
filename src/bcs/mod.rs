use crate::iop::transcript::{SubprotocolTranscript, Transcript};
use crate::iop::{
    EncodedProverMessage, IOPProverMessage, IOPVerifierMessage, MTParameters, MessageTree,
    SubprotocolMessage,
};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::borrow::Borrow;

/// BCS implementation of prover transcript
pub struct BCSTranscript<
    P: MTConfig,
    S: CryptographicSponge,
    L: Borrow<P::Leaf>,
    V: IOPVerifierMessage<S>,
> {
    encoded_prover_messages: MessageTree<EncodedProverMessage<P, L>>,
    verifier_messages: MessageTree<V>,
    sponge: S,
}

impl<P, S, L, V> BCSTranscript<P, S, L, V>
where
    P: MTConfig,
    S: CryptographicSponge,
    L: Borrow<P::Leaf>,
    V: IOPVerifierMessage<S>,
    P::InnerDigest: Absorb,
{
    /// Return a new BCS transcript.
    pub fn new(sponge: S) -> Self {
        Self {
            encoded_prover_messages: MessageTree::new(),
            verifier_messages: MessageTree::new(),
            sponge,
        }
    }

    // TODO: add a function to generate proof.
}

impl<P, S, L, V> Transcript<P, S> for BCSTranscript<P, S, L, V>
where
    P: MTConfig,
    S: CryptographicSponge,
    L: Borrow<P::Leaf>,
    V: IOPVerifierMessage<S>,
    P::InnerDigest: Absorb,
{
    type Leaf = L;
    type VerifierMessage = V;
    type StateWithoutSponge = (MessageTree<EncodedProverMessage<P, L>>, MessageTree<V>);

    fn send_prover_message(
        &mut self,
        msg: impl IOPProverMessage<P, Leaf = Self::Leaf>,
        mt_params: &MTParameters<P>,
    ) -> Result<(), Error> {
        // encode the message
        let encoded = msg.encode(mt_params)?;
        // calculate the mt root
        let mt_root = encoded.merkle_tree.root();
        // absorb the mt root
        self.sponge.absorb(&mt_root);
        // store the encoded prover message for generating proof
        self.encoded_prover_messages
            .push_current_protocol_message(encoded);

        Ok(())
    }

    fn squeeze_verifier_message(&mut self) -> Result<Self::VerifierMessage, Error> {
        let vm = Self::VerifierMessage::from_sponge(&mut self.sponge);
        // store the verifier message for later decision phase
        self.verifier_messages
            .push_current_protocol_message(vm.clone());
        Ok(vm)
    }

    fn into_subprotocol<VM>(self, subprotocol_id: usize) -> SubprotocolTranscript<P, S, Self, VM>
    where
        VM: IOPVerifierMessage<S> + SubprotocolMessage<Self::VerifierMessage, S>,
    {
        // extract sponge
        let sponge = self.sponge;
        // extract state
        let state_without_sponge = (self.encoded_prover_messages, self.verifier_messages);
        // create subprotocol transcript
        SubprotocolTranscript::new(subprotocol_id, state_without_sponge, sponge)
    }

    fn recover_from_subprotocol<VM>(subprotocol: SubprotocolTranscript<P, S, Self, VM>) -> Self
        where
            VM: IOPVerifierMessage<S> + SubprotocolMessage<Self::VerifierMessage, S>
    {
        let sponge = subprotocol.sponge_from_parent;
        let parent_state = subprotocol.parent_state;
        // recover
        let mut transcript = Self {
            encoded_prover_messages: parent_state.0,
            verifier_messages: parent_state.1,
            sponge,
        };
        // append subprotocol message
        transcript
            .encoded_prover_messages
            .receive_subprotocol_messages(subprotocol.id, subprotocol.encoded_prover_messages);
        transcript
            .verifier_messages
            .receive_subprotocol_messages(subprotocol.id, subprotocol.verifier_messages);
        transcript
    }
}
