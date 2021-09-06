use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::constraints::{AbsorbGadget, SpongeWithGadget};
use ark_sponge::Absorb;
use ark_std::vec::Vec;

use crate::bcs::constraints::transcript::SimulationTranscriptVar;
use crate::bcs::transcript::{MessageBookkeeper, NameSpace};
use crate::iop::constraints::message::{SuccinctRoundOracleVarView, VerifierMessageVar};
use crate::iop::verifier::IOPVerifier;

/// Defines prover and verifier message variable.
pub mod message;

/// Constraints for IOP Verifier.
///
/// The verifier for public coin IOP has two phases.
/// * **Commit Phase**: Verifier send message that is uniformly sampled from a random oracle. Verifier
/// will receive prover oracle, that can use used to query later. This protocol relies on public coin assumption
/// described in [BCS16, section 4.1](https://eprint.iacr.org/2016/116.pdf#subsection.4.1), that the verifier does not
/// main state and postpones any query to after the commit phase.
/// * **Query And Decision Phase**: Verifier sends query and receive answer from message oracle.
pub trait IOPVerifierWithGadget<S, CF>: IOPVerifier<S, CF>
where
    S: SpongeWithGadget<CF>,
    CF: PrimeField + Absorb,
{
    /// Verifier Output
    type VerifierOutputVar;
    /// Verifier State.
    type VerifierStateVar;
    /// Public Input Variable
    type PublicInputVar: ?Sized;

    /// Simulate interaction with prover in commit phase, reconstruct verifier messages and verifier state
    /// using the sponge provided in the simulation transcript. Returns the verifier state for query and decision phase.
    ///
    /// When writing test, use `transcript.check_correctness` after calling this method to verify the correctness
    /// of this method.
    fn restore_from_commit_phase_var<MT: Config, MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>>(
        namespace: &NameSpace,
        public_input: &Self::PublicInputVar,
        transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
        verifier_parameter: &Self::VerifierParameter,
    ) -> Result<(), SynthesisError>
    where
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<CF>;

    /// Returns the initial state for query and decision phase.
    fn initial_state_for_query_and_decision_phase_var(
        public_input: &Self::PublicInputVar,
    ) -> Result<Self::VerifierStateVar, SynthesisError>;

    /// Query the oracle using the random oracle. Run the verifier code, and return verifier output that
    /// is valid if prover claim is true. Verifier will return an error if prover message is obviously false,
    /// or oracle cannot answer the query.
    ///
    /// To access prover message oracle and previous verifier messages of current namespace, use bookkeeper.
    fn query_and_decide_var(
        cs: ConstraintSystemRef<CF>,
        namespace: &NameSpace,
        verifier_parameter: &Self::VerifierParameter,
        verifier_state: &mut Self::VerifierStateVar,
        random_oracle: &mut S::Var,
        prover_message_oracle: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        verifier_messages: &[Vec<VerifierMessageVar<CF>>],
        bookkeeper: &MessageBookkeeper,
    ) -> Result<Self::VerifierOutputVar, SynthesisError>;
}
