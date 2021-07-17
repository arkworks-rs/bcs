use crate::iop::{IOPVerifierMessage, MessageTree, ProverMessageOracle};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_sponge::CryptographicSponge;
use ark_std::borrow::Borrow;

/// The verifier for public coin IOP has two phases.
/// * **Commit Phase**: Verifier send message that is uniformly sampled from a random oracle. Verifier
/// will receive prover oracle, that can use used to query later. Commit phase is already done in IOP
/// prover because this protocol is public coin and we have a random oracle.
/// * **Query And Decision Phase**: Verifier sends query and receive answer from message oracle.
pub trait IOPVerifier<P: MTConfig, S: CryptographicSponge> {
    /// TODO doc
    type Leaf: Borrow<P::Leaf> + Clone;
    /// TODO doc
    type VerifierOutput;
    /// TODO doc
    type VerifierMessage: IOPVerifierMessage<S>;

    /// Query the oracle using the random oracle. Run the verifier code, and return verifier output that
    /// is valid if prover claim is true. Verifier will return an error if prover message is obviously false,
    /// or oracle cannot answer the query.
    fn query_and_decision(
        random_oracle: &mut S,
        prover_message_oracle: &mut MessageTree<impl ProverMessageOracle<P, Self::Leaf>>,
        previous_verifier_messages: MessageTree<Self::VerifierMessage>,
    ) -> Result<Self::VerifierOutput, Error>;
}
