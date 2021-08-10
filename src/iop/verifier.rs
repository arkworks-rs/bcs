use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

use crate::bcs::message::{RoundOracle, VerifierMessage};
use crate::bcs::transcript::{MessageBookkeeper, NameSpace, SimulationTranscript};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;

/// The verifier for public coin IOP has two phases.
/// * **Commit Phase**: Verifier send message that is uniformly sampled from a random oracle. Verifier
/// will receive prover oracle, that can use used to query later. This protocol relies on public coin assumption
/// described in [BCS16, section 4.1](https://eprint.iacr.org/2016/116.pdf#subsection.4.1), that the verifier does not
/// main state and postpones any query to after the commit phase.
/// * **Query And Decision Phase**: Verifier sends query and receive answer from message oracle.
///
pub trait IOPVerifier<S: CryptographicSponge, F: PrimeField + Absorb> {
    /// TODO doc
    type VerifierOutput;
    /// Verifier Parameter
    type VerifierParameter: ?Sized;
    /// Verifier state. May contain input.
    type VerifierState;
    /// Public input
    type PublicInput: ?Sized;

    /// Simulate interaction with prover in commit phase, reconstruct verifier messages and verifier state
    /// using the sponge provided in the simulation transcript. Returns the verifier state for query and decision phase.
    ///
    /// When writing test, use `transcript.check_correctness` after calling this method to verify the correctness
    /// of this method.
    fn restore_state_from_commit_phase<MT: MTConfig<Leaf = [F]>>(
        namespace: &NameSpace,
        public_input: &Self::PublicInput,
        transcript: &mut SimulationTranscript<MT, S, F>,
        verifier_parameter: &Self::VerifierParameter,
    ) where
        MT::InnerDigest: Absorb;

    /// Returns the initial state for query and decision phase.
    fn initial_state_for_query_and_decision_phase(
        public_input: &Self::PublicInput,
    ) -> Self::VerifierState;

    /// Query the oracle using the random oracle. Run the verifier code, and return verifier output that
    /// is valid if prover claim is true. Verifier will return an error if prover message is obviously false,
    /// or oracle cannot answer the query.
    ///
    /// To access prover message oracle and previous verifier messages of current namespace, use bookkeeper.
    fn query_and_decide<'a, O: 'a + RoundOracle<F>>(
        namespace: &NameSpace,
        verifier_parameter: &Self::VerifierParameter,
        verifier_state: &mut Self::VerifierState,
        random_oracle: &mut S,
        prover_message_oracle: impl IntoIterator<Item = &'a mut O>,
        verifier_messages: &[Vec<VerifierMessage<F>>],
        bookkeeper: &MessageBookkeeper,
    ) -> Result<Self::VerifierOutput, Error>;
}
