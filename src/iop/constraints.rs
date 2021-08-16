use crate::bcs::constraints::message::{SuccinctRoundOracleVarView, VerifierMessageVar};
use crate::bcs::constraints::transcript::SimulationTranscriptVar;
use crate::bcs::transcript::{MessageBookkeeper, NameSpace};
use crate::iop::verifier::IOPVerifier;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{SynthesisError, ConstraintSystemRef};
use ark_sponge::constraints::{AbsorbGadget, SpongeWithGadget};
use ark_sponge::Absorb;

pub trait IOPVerifierWithGadget<S, CF>: IOPVerifier<S, CF>
where
    S: SpongeWithGadget<CF>,
    CF: PrimeField + Absorb,
{
    type VerifierOutputVar;
    type VerifierStateVar;
    type PublicInputVar: ?Sized;

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
