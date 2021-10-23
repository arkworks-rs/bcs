use ark_crypto_primitives::merkle_tree::{constraints::ConfigGadget, Config};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_sponge::{
    constraints::{AbsorbGadget, SpongeWithGadget},
    Absorb,
};

use crate::{
    bcs::{constraints::transcript::SimulationTranscriptVar, transcript::NameSpace},
    iop::{
        constraints::message::{SuccinctRoundOracleVarView, VerifierMessageVar},
        message::MessagesCollection,
        verifier::IOPVerifier,
    },
};

/// Defines prover and verifier message variable.
pub mod message;

/// Constraints for IOP Verifier.
///
/// The verifier for public coin IOP has two phases.
/// * **Commit Phase**: Verifier send message that is uniformly sampled from a
///   random oracle. Verifier
/// will receive prover oracle, that can use used to query later. This protocol
/// relies on public coin assumption described in [BCS16, section 4.1](https://eprint.iacr.org/2016/116.pdf#subsection.4.1), that the verifier does not
/// main state and postpones any query to after the commit phase.
/// * **Query And Decision Phase**: Verifier sends query and receive answer from
///   message oracle.
pub trait IOPVerifierWithGadget<S, CF>: IOPVerifier<S, CF>
where
    S: SpongeWithGadget<CF>,
    CF: PrimeField + Absorb,
{
    /// Verifier Output
    type VerifierOutputVar;
    /// Public Input Variable
    type PublicInputVar: ?Sized;

    /// Simulate interaction with prover in commit phase, reconstruct verifier
    /// messages and verifier state using the sponge provided in the
    /// simulation transcript. Returns the verifier state for query and decision
    /// phase.
    ///
    /// When writing test, use `transcript.check_correctness` after calling this
    /// method to verify the correctness of this method.
    fn register_iop_structure_var<MT: Config, MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>>(
        namespace: NameSpace,
        transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
        verifier_parameter: &Self::VerifierParameter,
    ) -> Result<(), SynthesisError>
    where
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<CF>;

    /// Query the oracle using the random oracle. Run the verifier code, and
    /// return verifier output that is valid if prover claim is true.
    /// Verifier will return an error if prover message is obviously false,
    /// or oracle cannot answer the query.
    ///
    /// To access prover message oracle and previous verifier messages of
    /// current namespace, use bookkeeper.
    fn query_and_decide_var(
        cs: ConstraintSystemRef<CF>,
        namespace: NameSpace,
        verifier_parameter: &Self::VerifierParameter,
        public_input_var: &Self::PublicInputVar,
        oracle_refs: &Self::OracleRefs,
        sponge: &mut S::Var,
        messages_in_commit_phase: &mut MessagesCollection<
            SuccinctRoundOracleVarView<CF>,
            VerifierMessageVar<CF>,
        >,
    ) -> Result<Self::VerifierOutputVar, SynthesisError>;
}
