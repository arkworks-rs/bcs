use crate::bcs::constraints::message::{SuccinctRoundOracleVarView, VerifierMessageVar};
use crate::bcs::constraints::transcript::SimulationTranscriptVar;
use crate::ldt_trait::{NoLDT, LDT};
use crate::Error;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_sponge::constraints::{AbsorbGadget, SpongeWithGadget};
use ark_sponge::Absorb;

pub trait LDTWithGadget<CF: PrimeField + Absorb>: LDT<CF> {
    fn restore_from_commit_phase_var<MT, MTG, S>(
        param: &Self::LDTParameters,
        codewords_oracles: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
    ) -> Result<(), Error>
    where
        MT: Config,
        MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>,
        S: SpongeWithGadget<CF>,
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<CF>;

    fn query_and_decide_var<S: SpongeWithGadget<CF>>(
        param: &Self::LDTParameters,
        random_oracle: &mut S,
        codewords_oracles: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        ldt_prover_message_oracles: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        ldt_verifier_messages: &[Vec<VerifierMessageVar<CF>>],
    ) -> Result<(), Error>;
}

impl<CF: PrimeField + Absorb> LDTWithGadget<CF> for NoLDT<CF> {
    fn restore_from_commit_phase_var<MT, MTG, S>(
        param: &Self::LDTParameters,
        codewords_oracles: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
    ) -> Result<(), Error>
    where
        MT: Config,
        MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>,
        S: SpongeWithGadget<CF>,
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<CF>,
    {
        // do nothing
        Ok(())
    }

    fn query_and_decide_var<S: SpongeWithGadget<CF>>(
        param: &Self::LDTParameters,
        random_oracle: &mut S,
        codewords_oracles: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        ldt_prover_message_oracles: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        ldt_verifier_messages: &[Vec<VerifierMessageVar<CF>>],
    ) -> Result<(), Error> {
        // do nothing
        Ok(())
    }
}
