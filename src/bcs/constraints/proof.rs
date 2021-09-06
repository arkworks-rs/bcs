use crate::bcs::constraints::message::SuccinctRoundOracleVar;
use crate::bcs::prover::BCSProof;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_crypto_primitives::PathVar;
use ark_ff::PrimeField;
use ark_r1cs_std::alloc::{AllocVar, AllocationMode};
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_sponge::constraints::AbsorbGadget;
use ark_sponge::Absorb;
use ark_std::borrow::Borrow;
use ark_std::vec::Vec;

/// Variable for BCS Proof.
/// BCSProof contains all prover messages that use succinct oracle, and thus is itself succinct.
pub struct BCSProofVar<MT, MTG, CF>
where
    MT: Config,
    MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>,
    CF: PrimeField,
    MT::InnerDigest: Absorb,
    MTG::InnerDigest: AbsorbGadget<CF>,
{
    /// Messages sent by prover in commit phase. Each item in the vector represents a list of
    /// message oracles (reed solomon codes go first) with same length. The length constraints do not hold for short messages (IP message).
    /// All non-IP messages in the same prover round share the same merkle tree. Each merkle tree leaf is
    /// a vector which each element correspond to the same coset of different oracles.
    pub prover_iop_messages_by_round: Vec<SuccinctRoundOracleVar<CF>>,
    /// Merkle tree roots for all prover messages (including main prover and ldt prover).
    pub prover_messages_mt_root: Vec<Option<MTG::InnerDigest>>,
    /// Merkle tree paths for queried prover messages in main protocol.
    /// `prover_messages_mt_path[i][j]` is the path for jth query at ith round of prover message.
    pub prover_oracles_mt_path: Vec<Vec<PathVar<MT, CF, MTG>>>,
}

impl<MT, MTG, CF> AllocVar<BCSProof<MT, CF>, CF> for BCSProofVar<MT, MTG, CF>
where
    MT: Config,
    MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>,
    CF: PrimeField,
    MT::InnerDigest: Absorb,
    MTG::InnerDigest: AbsorbGadget<CF>,
{
    fn new_variable<T: Borrow<BCSProof<MT, CF>>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let native = f()?;
        let native = native.borrow();
        let cs = cs.into();
        let prover_iop_messages_by_round = Vec::<SuccinctRoundOracleVar<CF>>::new_variable(
            cs.clone(),
            || Ok(native.prover_iop_messages_by_round.clone()),
            mode,
        )?;
        let prover_messages_mt_root = native
            .prover_messages_mt_root
            .iter()
            .map(|root| {
                root.as_ref().map_or(Ok(None), |root| {
                    Ok(Some(MTG::InnerDigest::new_variable(
                        cs.clone(),
                        || Ok(root),
                        mode,
                    )?))
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let prover_oracles_mt_path = native
            .prover_oracles_mt_path
            .iter()
            .map(|paths| {
                Vec::<PathVar<MT, CF, MTG>>::new_variable(cs.clone(), || Ok(paths.as_slice()), mode)
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            prover_iop_messages_by_round,
            prover_messages_mt_root,
            prover_oracles_mt_path,
        })
    }
}
