use crate::bcs::oracle::MessageFetchingOracle;
use crate::bcs::Transcript;
use crate::iop::prover::IOPProver;
use crate::iop::verifier::IOPVerifier;
use crate::iop::MessageTree;
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

/// TODO doc
pub struct BCSProof<MT, F, FinalHash>
where
    MT: MTConfig,
    F: PrimeField,
    MT::InnerDigest: Absorb,
    FinalHash: Clone,
{
    prover_message_oracle: MessageTree<MessageFetchingOracle<MT, F>>,
    final_hash: FinalHash,
}

impl<MT, F, FinalHash> BCSProof<MT, F, FinalHash>
where
    MT: MTConfig<Leaf = F>,
    F: PrimeField,
    MT::InnerDigest: Absorb,
    FinalHash: Clone,
{
    /// Generate proof
    pub fn generate<V, S, P>(
        sponge: S,
        prover_parameter: &P::ProverParameter,
        verifier_parameter: &P::VerifierParameter,
        final_hasher: fn(&mut S) -> FinalHash,
    ) -> Result<Self, Error>
    where
        V: IOPVerifier<MT, S, F, VerifierParameter = P::VerifierParameter>,
        S: CryptographicSponge,
        P: IOPProver<MT, S, F>,
    {
        // create a BCS transcript
        let mut transcript = Transcript::new(sponge);
        // run prover code
        transcript = P::prove(transcript, prover_parameter, verifier_parameter);
        // convert transcript to prover message oracle
        let mut recording_oracle = transcript
            .encoded_prover_messages
            .map_into(|x| x.into_oracle());
        let mut sponge = transcript.sponge;
        // run verifier code
        V::query_and_decision(
            &mut sponge,
            &mut recording_oracle,
            transcript.verifier_messages,
        )?;
        // convert oracle to message fetching oracle
        let fetching_oracle = recording_oracle.map_into(|x| x.into_message_fetching_oracle());
        // compute final hash
        let final_hash = final_hasher(&mut sponge);

        Ok(Self {
            prover_message_oracle: fetching_oracle,
            final_hash,
        })
    }
}
