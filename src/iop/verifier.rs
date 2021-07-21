use crate::iop::{MessageTree, ProverMessageOracle};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::CryptographicSponge;

/// The verifier for public coin IOP has two phases.
/// * **Commit Phase**: Verifier send message that is uniformly sampled from a random oracle. Verifier
/// will receive prover oracle, that can use used to query later. Commit phase is already done in IOP
/// prover because this protocol is public coin and we have a random oracle.
/// * **Query And Decision Phase**: Verifier sends query and receive answer from message oracle.
pub trait IOPVerifier<P: MTConfig, S: CryptographicSponge, F: PrimeField> {
    /// TODO doc
    type VerifierOutput;
    /// Verifier Parameter
    type VerifierParameter: ?Sized;

    // /// Given access to prover merkle tree root given in `prover_message_oracle`, and a random oracle,
    // /// reconstruct sent verifier messages. In case of subprotocol, simply call `SubprotocolVerifier::reconstruct_verifier_messages`,
    // /// and Convert subprotocol message to current message using `map_into`.
    // ///
    // /// This building block should be same as
    // fn reconstruct_verifier_messages(
    //     random_oracle: &mut S,
    //     prover_message_oracle: &MessageTree<impl ProverMessageOracle<P, Self::Leaf>>,
    //     verifier_parameter: &Self::VerifierParameter
    // ) -> MessageTree<Self::VerifierMessage>;

    /// Query the oracle using the random oracle. Run the verifier code, and return verifier output that
    /// is valid if prover claim is true. Verifier will return an error if prover message is obviously false,
    /// or oracle cannot answer the query.
    fn query_and_decision(
        random_oracle: &mut S,
        prover_message_oracle: &mut MessageTree<impl ProverMessageOracle<P, F>>,
        previous_verifier_messages: MessageTree<Vec<F>>,
    ) -> Result<Self::VerifierOutput, Error>;
}
