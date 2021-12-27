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

use crate::{
    bcs::constraints::transcript::SimulationTranscriptVar,
    iop::{
        bookkeeper::NameSpace, constraints::message::MessagesCollectionVar, message::MsgRoundRef,
    },
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
        namespace: NameSpace,
        param: &Self::LDTParameters,
        num_rs_oracles: usize,
        transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
    ) -> Result<(), SynthesisError>
    where
        MT: Config,
        MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>,
        S: SpongeWithGadget<CF>,
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<CF>;

    /// R1CS gadget for `query_and_decide`.
    ///
    /// Verify `codewords` is low-degree, given the succinct codewords oracle
    /// and proof.
    fn query_and_decide_var<S: SpongeWithGadget<CF>>(
        namespace: NameSpace,
        param: &Self::LDTParameters,
        sponge: &mut S::Var,
        codewords: &[MsgRoundRef],
        // TODO: add virtual oracle here
        transcript_messages: &mut MessagesCollectionVar<CF>,
    ) -> Result<(), SynthesisError>;
}

impl<CF: PrimeField + Absorb> LDTWithGadget<CF> for NoLDT<CF> {
    fn register_iop_structure_var<MT, MTG, S>(
        _namespace: NameSpace,
        _param: &Self::LDTParameters,
        _num_rs_oracles: usize,
        _transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
    ) -> Result<(), SynthesisError>
    where
        MT: Config,
        MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>,
        S: SpongeWithGadget<CF>,
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<CF>,
    {
        Ok(())
    }

    fn query_and_decide_var<S: SpongeWithGadget<CF>>(
        _namespace: NameSpace,
        _param: &Self::LDTParameters,
        _sponge: &mut S::Var,
        codewords: &[MsgRoundRef],
        // TODO: add virtual oracle here
        transcript_messages: &mut MessagesCollectionVar<CF>,
    ) -> Result<(), SynthesisError> {
        // nop, but we need to check that all codewords have no RS codes
        let no_rs_code = codewords.iter().all(|round| {
            transcript_messages
                .get_prover_round_info(*round)
                .num_reed_solomon_codes_oracles()
                == 0
        });
        assert!(
            no_rs_code,
            "NoLDT enforces that main protocol does not send any RS code."
        );
        Ok(())
    }
}
