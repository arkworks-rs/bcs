use crate::bcs::message::{SuccinctOracle, ProverMessage};
use crate::iop::prover::IOPProver;
use crate::iop::verifier::IOPVerifier;
use crate::iop::MTHashParameters;
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};
use crate::ldt_trait::LDT;

/// BCSProof contains all prover messages that use succinct oracle, and thus is itself succinct.
#[derive(Derivative)]
#[derivative(Clone(bound="MT: MTConfig, F: PrimeField, FinalHash: Clone, L: LDT<MT, F>"))]
pub struct BCSProof<MT, F, L, FinalHash>
    where
        MT: MTConfig,
        F: PrimeField,
        L: LDT<MT, F>,
        MT::InnerDigest: Absorb,
        FinalHash: Clone,
{
    prover_message: Vec<ProverMessage<MT, F, SuccinctOracle<MT, F>>>,
    ldt_proof: L::LDTProof,
    final_hash: FinalHash,
}

impl<MT, F, L, FinalHash> BCSProof<MT, F, L, FinalHash>
where
    MT: MTConfig<Leaf = F>,
    F: PrimeField,
    L: LDT<MT, F>,
    MT::InnerDigest: Absorb,
    FinalHash: Clone,
{
    /// Generate proof
    pub fn generate<V, S, P>(
        sponge: S,
        prover_state: &mut P::ProverState,
        prover_parameter: &P::ProverParameter,
        verifier_parameter: &P::VerifierParameter,
        hash_params: MTHashParameters<MT>,
        final_hasher: fn(&mut S) -> FinalHash,
    ) -> Result<Self, Error>
    where
        V: IOPVerifier<MT, S, F, VerifierParameter = P::VerifierParameter>,
        S: CryptographicSponge,
        P: IOPProver<MT, S, F, L>,
    {
        todo!()
        // // create a BCS transcript
        // let mut transcript = Transcript::new(sponge, hash_params);
        // // run prover code
        // transcript = P::prove(prover_state, transcript, prover_parameter, verifier_parameter);
        // // run LDT on message oracle
        // {
        //     // TODO
        // }
        // // convert transcript to prover message oracle
        // let mut recording_oracle = transcript
        //     .prover_message_oracles; todo!();
        // let mut sponge = transcript.sponge;
        // // run verifier code
        // V::query_and_decision(
        //     &mut sponge,
        //     &mut recording_oracle,
        //     transcript.verifier_messages,
        // )?;
        // // convert oracle to message fetching oracle
        // let fetching_oracle = recording_oracle.map_into(|x| x.into_message_fetching_oracle());
        // // compute final hash
        // let final_hash = final_hasher(&mut sponge);
        //
        // Ok(Self {
        //     prover_message_oracle: fetching_oracle,
        //     final_hash,
        // })
    }
}

fn le_bits_to_usize(bits: &[bool]) -> usize {
    let mut result = 0;
    bits.iter().for_each(|&x| {
        result <<= 1;
        result |= x as usize;
    });
    result
}
