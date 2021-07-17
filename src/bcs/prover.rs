use crate::bcs::oracle::MessageFetchingOracle;
use crate::bcs::BCSTranscript;
use crate::iop::prover::IOPProver;
use crate::iop::verifier::IOPVerifier;
use crate::iop::MessageTree;
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::borrow::Borrow;

/// TODO doc
pub struct BCSProof<MT, S, P, FinalHash>
where
    MT: MTConfig,
    S: CryptographicSponge,
    P: IOPProver<MT, S>,
    MT::InnerDigest: Absorb,
    FinalHash: Clone,
{
    prover_message_oracle: MessageTree<MessageFetchingOracle<MT, P::Leaf>>,
    final_hash: FinalHash,
}

impl<MT, S, P, FinalHash> BCSProof<MT, S, P, FinalHash>
where
    MT: MTConfig,
    S: CryptographicSponge,
    P: IOPProver<MT, S>,
    MT::InnerDigest: Absorb,
    FinalHash: Clone,
{
    /// Generate proof
    pub fn generate<
        V: IOPVerifier<MT, S, Leaf = P::Leaf, VerifierMessage = P::VerifierMessage>,
        PP: Borrow<P::ProverParameter>,
    >(
        param: PP,
        sponge: S,
        final_hasher: fn(&mut S) -> FinalHash,
    ) -> Result<Self, Error> {
        // create a BCS transcript
        let mut transcript = BCSTranscript::new(sponge);
        // run prover code
        P::prove(&mut transcript, param);
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
