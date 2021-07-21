/// Defines a prover message oracle.
pub mod oracle;
/// TODO doc
pub mod prover;
mod verifier;

use crate::iop::{
    EncodedProverMessage, IOPProverMessage, MTParameters, MessageTree, SubprotocolID,
};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};

/// A communication protocol for IOP prover.
pub struct Transcript<P: MTConfig, S: CryptographicSponge, F: PrimeField> {
    /// Message sent by prover in commit phase.
    encoded_prover_messages: MessageTree<EncodedProverMessage<P, F>>,
    /// Sampled Message sent by verifier in commit phase.
    verifier_messages: MessageTree<Vec<F>>,
    /// Random Oracle to sample verifier messages.
    sponge: S,
}

/// Parent transcript where subprotocol is running.
pub struct TranscriptWithoutSponge<P: MTConfig, F: PrimeField> {
    // Message sent by prover in commit phase.
    encoded_prover_messages: MessageTree<EncodedProverMessage<P, F>>,
    /// Sampled Message sent by verifier in commit phase.
    verifier_messages: MessageTree<Vec<F>>,
}

impl<P, S, F> Transcript<P, S, F>
where
    P: MTConfig<Leaf = F>,
    S: CryptographicSponge,
    F: PrimeField,
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

    /// Send prover message to transcript. This function will
    /// encode this message to merkle tree.
    pub fn send_prover_message(
        &mut self,
        msg: impl IOPProverMessage<P, F>,
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

    /// Squeeze sampled verifier message from transcript.
    fn squeeze_verifier_message(&mut self, field_size: &[FieldElementSize]) -> Vec<F> {
        let msg = self.sponge.squeeze_field_elements_with_sizes(field_size);
        // store the verifier message for later decision phase
        self.verifier_messages
            .push_current_protocol_message(msg.clone());
        msg
    }

    /// Create a branch of `self` as a transcript to be used for subprotocol.
    /// Returns the transcript for subprotocol, and current transcript without sponge.
    fn create_branch(self) -> (Self, TranscriptWithoutSponge<P, F>) {
        let sponge = self.sponge;
        let branched = TranscriptWithoutSponge {
            encoded_prover_messages: self.encoded_prover_messages,
            verifier_messages: self.verifier_messages,
        };
        (Self::new(sponge), branched)
    }
}

impl<P: MTConfig, F: PrimeField> TranscriptWithoutSponge<P, F> {
    /// Merge the subprotocol transcript to current transcript to updating the sponge state
    fn merge_branch<S: CryptographicSponge>(
        mut self,
        branch: Transcript<P, S, F>,
        subprotocol_id: SubprotocolID,
    ) -> Transcript<P, S, F> {
        let sponge = branch.sponge;
        // store the subprotocol messages to current transcript
        self.verifier_messages
            .receive_subprotocol_messages(subprotocol_id, branch.verifier_messages);
        self.encoded_prover_messages
            .receive_subprotocol_messages(subprotocol_id, branch.encoded_prover_messages);
        Transcript {
            encoded_prover_messages: self.encoded_prover_messages,
            verifier_messages: self.verifier_messages,
            sponge,
        }
    }
}
