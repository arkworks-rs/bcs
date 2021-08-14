use crate::bcs::constraints::message::SuccinctRoundOracleVar;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_crypto_primitives::PathVar;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_sponge::constraints::AbsorbGadget;
use ark_sponge::Absorb;

pub struct BCSProofVar<MT, MTG, CF>
where
    MT: Config,
    MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>,
    CF: PrimeField,
    MT::InnerDigest: Absorb,
    MTG::InnerDigest: AbsorbGadget<CF>,
{
    pub prover_iop_messages_by_round: Vec<SuccinctRoundOracleVar<CF>>,
    pub prover_messages_mt_root: Vec<Option<MTG::InnerDigest>>,
    pub prover_oracles_mt_path: Vec<Vec<PathVar<MT, CF, MTG>>>,
}
