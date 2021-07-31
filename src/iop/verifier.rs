use ark_ff::PrimeField;
use ark_sponge::CryptographicSponge;

use crate::bcs::message::{MessageOracle, ProverMessagesInRound, VerifierMessage};
use crate::bcs::transcript::{MessageBookkeeper, NameSpace};
use crate::Error;

/// The verifier for public coin IOP has two phases.
/// * **Commit Phase**: Verifier send message that is uniformly sampled from a random oracle. Verifier
/// will receive prover oracle, that can use used to query later. Commit phase is already done in IOP
/// prover because this protocol is public coin and we have a random oracle.
/// * **Query And Decision Phase**: Verifier sends query and receive answer from message oracle.
pub trait IOPVerifier<S: CryptographicSponge, F: PrimeField> {
    /// TODO doc
    type VerifierOutput;
    /// Verifier Parameter
    type VerifierParameter: ?Sized;

    /// Simulate interaction with prover in commit phase, reconstruct verifier messages using the sponge
    /// provided in the simulation transcript.
    ///
    /// ## Example
    /// Suppose the prover code in commit phase is as follows:
    /// ```ignore
    /// let msg1 = self.calculate_msg1();
    /// transcript.send_univariate_polynomial(ns, bound, &msg1);
    /// let vmsg = transcript.squeeze_verifier_bytes(...);
    /// let msg2 = self.calculate_msg2(vmsg);
    /// transcript.send_oracle_evaluations(ns, &msg2, domain, bound);
    /// let msg3 = self.calculate_msg3(vmsg, msg2);
    /// transcript.send_ip_message(ns, &msg3);
    /// ```
    ///
    /// Then, the corresponding simulation code should be
    /// ```ignore
    /// transcript.receive_oracle_evaluation(ns, bound);
    /// transcript.squeeze_verifier_bytes(...);
    /// transcript.receive_oracle_evaluation(ns, bound);
    /// transcript.receive_ip_message(ns)
    /// ```
    // fn reconstruct_verifier_messages<L: LDT<P, F, S>>(
    //     namespace: &NameSpace,
    //     public_input: Self::PublicInput,
    //     transcript: &mut SimulationTranscript<P, S, F, L>,
    //     verifier_parameter: &Self::VerifierParameter
    // );

    /// Query the oracle using the random oracle. Run the verifier code, and return verifier output that
    /// is valid if prover claim is true. Verifier will return an error if prover message is obviously false,
    /// or oracle cannot answer the query.
    ///
    /// To access prover message oracle and previous verifier messages of current namespace, use bookkeeper.
    fn query_and_decide<Oracle: MessageOracle<F>>(
        namespace: &NameSpace,
        verifier_parameter: &Self::VerifierParameter,
        random_oracle: &mut S,
        prover_message_oracle: &[&mut ProverMessagesInRound<F, Oracle>],
        verifier_messages: &[Vec<VerifierMessage<F>>],
        bookkeeper: &MessageBookkeeper,
    ) -> Result<Self::VerifierOutput, Error>;
}
