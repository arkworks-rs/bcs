use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use crate::iop::{IOPVerifierMessage, IOPProverMessage, MessageTree, EncodedProverMessage, MTParameters};
use ark_sponge::{CryptographicSponge, Absorb};
use crate::Error;
use ark_std::borrow::Borrow;

/// `Transcript` serves as a communication protocol for prover to interact with verifier.
/// User do not need to implement `Transcript` by themselves. There are two implementations in the crate:
/// * `BCSTranscript`: transcript used for BCS
/// * `SubprotocolTranscript`: a wrapper transcript used for subprotocol.
///
/// `Transcript` stores the prover message, feeds merkle tree root of that message to sponge, and samples verifier message from sponge.
///
/// `P` is the merkle tree config, and `S` is the random oracle that transcript uses.
pub trait Transcript<P: MTConfig, S: CryptographicSponge>
where P::InnerDigest: Absorb
{
    /// Type of leaf used for merkle tree.
    type Leaf: Borrow<P::Leaf>;
    /// Type of public coin verifier message that can be squeezed from sponge.
    type VerifierMessage: IOPVerifierMessage<S>;

    /// Send prover message to the protocol. Do not send subprotocol message using this method.
    fn send_prover_message(&mut self, msg: impl IOPProverMessage<P, Leaf=Self::Leaf>, mt_params: &MTParameters<P>) -> Result<(), Error>;

    /// Send verifier message to the protocol. Do not squeeze subprotocl message using this method.
    fn squeeze_verifier_message(&mut self) -> Result<Self::VerifierMessage, Error>;

    // /// Convert current transcript to subprotocol transcript, so that current transcript can be
    // /// used by subprotocol.
    // fn into_subprotocol_transcript(self) -> Self::SubprotocolTranscript<Leaf=Self::Leaf>;

    /// Returns a mutable reference to the random oracle used by the transcript.
    /// This function should not be called by prover.
    /// TODO: this is only used by subprotocol. Instead, let subprotocol own this random oracle.
    /// And when convert back, return the ownership.
    // fn random_oracle(&mut self) -> &mut S;

    /// When a subprotocol has ended, the subprotocol transcript will send all encoded prover messages (as a vector of leaf)
    /// to its parent protocol using this function.
    /// This function should not be called by prover.
    fn _attach_subprotocol_prover_messages(&mut self, subprotocol_id: usize, messages: MessageTree<EncodedProverMessage<P, Self::Leaf>>);

    /// When a subprotocol has ended, the subprotocol transcript will send all verifier messages
    /// to its parent protocol using this function.
    /// This function should not be called by prover.
    fn _attach_subprotocol_verifier_messages(&mut self, subprotocol_id: usize, messages: MessageTree<Self::VerifierMessage>);



    // TODO: Add transform to subprotocol transcript
    // TODO: if current transcript is subprotocol transcript, all stored message will be transformed to parent.

    // some way: define a wrapper transcript. Return the wrapper transcript.
}

// pub struct SubprotocolTranscript<P: MTConfig, S: CryptographicSponge, T: Transcript<P, S>> {
//
// }
//
// impl<P: MTConfig, S: CryptographicSponge, T: Transcript<P, S>, V: Ve> Transcript<P, S> for SubprotocolTranscript<P, S, T> {
//
// }


