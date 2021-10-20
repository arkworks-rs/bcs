/// LDT that runs FRI gadget on a random linear combination.
pub mod rl_ldt;

use ark_crypto_primitives::merkle_tree::{constraints::ConfigGadget, Config};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::SynthesisError;
use ark_sponge::{
    constraints::{AbsorbGadget, SpongeWithGadget},
    Absorb,
};
use ark_std::vec::Vec;

use crate::{
    bcs::constraints::transcript::SimulationTranscriptVar,
    iop::constraints::message::{SuccinctRoundOracleVarView, VerifierMessageVar},
    ldt::{NoLDT, LDT},
};

/// An extension trait of `LDT`. Any implementation of this trait have R1CS
/// gadget for LDT.
pub trait LDTWithGadget<CF: PrimeField + Absorb>: LDT<CF> {
    /// Simulate interaction with prover in commit phase, reconstruct verifier
    /// messages and verifier state using the sponge provided in the
    /// simulation transcript. Returns the verifier state for query and decision
    /// phase.
    /// * `num_codewords_oracles`: sum of number of codeword oracles in each
    ///   round.
    fn register_iop_structure_var<MT, MTG, S>(
        param: &Self::LDTParameters,
        num_codewords_oracles: usize,
        // TODO: add virtual oracle here
        transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
    ) -> Result<(), SynthesisError>
    where
        MT: Config,
        MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>,
        S: SpongeWithGadget<CF>,
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<CF>;

    /// Verify `codewords` is low-degree, given the succinct codewords oracle
    /// and proof. `codewords_oracles[i]` includes all oracles sent on round
    /// `i`.
    fn query_and_decide_var<S: SpongeWithGadget<CF>>(
        param: &Self::LDTParameters,
        random_oracle: &mut S::Var,
        codewords_oracles: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        // TODO: add virtual oracle here
        ldt_prover_message_oracles: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        ldt_verifier_messages: &[Vec<VerifierMessageVar<CF>>],
    ) -> Result<(), SynthesisError>;
}

impl<CF: PrimeField + Absorb> LDTWithGadget<CF> for NoLDT<CF> {
    fn register_iop_structure_var<MT, MTG, S>(
        _param: &Self::LDTParameters,
        _num_codewords_oracles: usize,
        _transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
    ) -> Result<(), SynthesisError>
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
        _param: &Self::LDTParameters,
        _random_oracle: &mut S::Var,
        _codewords_oracles: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        _ldt_prover_message_oracles: Vec<&mut SuccinctRoundOracleVarView<CF>>,
        _ldt_verifier_messages: &[Vec<VerifierMessageVar<CF>>],
    ) -> Result<(), SynthesisError> {
        // do nothing
        Ok(())
    }
}
