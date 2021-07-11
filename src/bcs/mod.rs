use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_sponge::{CryptographicSponge, Absorb};
use crate::iop::prover::Transcript;
use crate::iop::{IOPProverMessage, MessageTree, EncodedProverMessage, IOPVerifierMessage, MTParameters};
use crate::Error;
use ark_std::borrow::Borrow;
use ark_std::marker::PhantomData;

/// BCS implementation of prover transcript
pub struct BCSTranscript<P: MTConfig, S: CryptographicSponge, L: Borrow<P::Leaf>, V: IOPVerifierMessage<S>>
{
    encoded_prover_message: Vec<EncodedProverMessage<P, L>>,
    verifier_messages: Vec<V>,
    sponge: S,
    _marker: PhantomData<(P, S, L, V)>,
}

impl<P, S, L, V> BCSTranscript<P, S, L, V>
    where P: MTConfig, S: CryptographicSponge, L: Borrow<P::Leaf>, V: IOPVerifierMessage<S>, P::InnerDigest: Absorb
{
    /// Return a new BCS transcript.
    pub fn new(sponge: S) -> Self{
        todo!()
    }

    // TODO: add a function to generate proof.

    /// Store the squeezed verifier message to keep the verifier state.
    fn store_verify_direct_message(&mut self, vm: <Self as Transcript<P, S>>::VerifierMessage) -> Result<(), Error> {
        todo!()
    }

}


impl<P, S, L, V> Transcript<P, S> for BCSTranscript<P, S, L, V>
    where P: MTConfig, S: CryptographicSponge, L: Borrow<P::Leaf>, V: IOPVerifierMessage<S>,
    P::InnerDigest: Absorb
{
    type Leaf = L;
    type VerifierMessage = V;

    fn send_prover_message(&mut self, msg: impl IOPProverMessage<P, Leaf=Self::Leaf>, mt_params: &MTParameters<P>) -> Result<(), Error> {
        // encode the message
        let encoded = msg.encode(mt_params)?;
        // calculate the mt root
        let mt_root = encoded.merkle_tree.root();
        // absorb the mt root
        self.sponge.absorb(&mt_root);
        // store the encoded prover message for generating proof
        self.encoded_prover_message.push(encoded);

        Ok(())
    }

    fn squeeze_verifier_message(&mut self) -> Result<Self::VerifierMessage, Error> {
        let vm = Self::VerifierMessage::from_sponge(&mut self.sponge);
        // store the verifier message for later decision phase
        self.verifier_messages.push(vm.clone());
        Ok(vm)
    }

    fn _attach_subprotocol_prover_messages(&mut self, subprotocol_id: usize, messages: MessageTree<EncodedProverMessage<P, Self::Leaf>>) {
        todo!()
    }

    fn _attach_subprotocol_verifier_messages(&mut self, subprotocol_id: usize, messages: MessageTree<Self::VerifierMessage>) {
        todo!()
    }
}

