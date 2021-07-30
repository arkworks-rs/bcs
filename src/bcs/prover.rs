use crate::bcs::message::{ProverMessagesInRound, SuccinctOracle};
use crate::bcs::transcript::{Transcript, ROOT_NAMESPACE};
use crate::iop::prover::IOPProver;
use crate::iop::verifier::IOPVerifier;
use crate::iop::MTHashParameters;
use crate::ldt_trait::LDT;
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

/// BCSProof contains all prover messages that use succinct oracle, and thus is itself succinct.
#[derive(Derivative)]
#[derivative(Clone(
    bound = "MT: MTConfig, F: PrimeField,S: CryptographicSponge"
))]
pub struct BCSProof<MT, F, S>
where
    MT: MTConfig,
    F: PrimeField,
    S: CryptographicSponge,
    MT::InnerDigest: Absorb,
{
    /// Messages sent by prover in commit phase. Each item in the vector represents a list of
    /// message oracles with same length. The length constraints do not hold for short messages (IP message).
    /// All non-IP messages in the same prover round should share the same merkle tree. Each merkle tree leaf is
    /// a vector which each element correspond to the same location of different oracles.
    ///
    /// Prover succinct oracle message. If the user uses RSIOP, the oracles in last `n` rounds will be used for LDT with
    /// `n` queries.
    pub prover_messages: Vec<Vec<ProverMessagesInRound<MT, F, SuccinctOracle<MT, F>>>>,

    /// Prover messages used for LDT. If the prover is not RS-IOP, this vector should be empty.
    pub ldt_prover_messages: Vec<ProverMessagesInRound<MT, F, SuccinctOracle<MT, F>>>,
}

impl<MT, F, S> BCSProof<MT, F, S>
where
    MT: MTConfig<Leaf = F>,
    F: PrimeField,
    S: CryptographicSponge,
    MT::InnerDigest: Absorb,
{
    /// Generate proof
    pub fn generate<V, P, L>(
        sponge: S,
        prover_initial_state: &mut P::ProverState,
        prover_parameter: &P::ProverParameter,
        verifier_parameter: &V::VerifierParameter,
        ldt_params: &L::LDTParameters,
        hash_params: MTHashParameters<MT>,
        final_hasher: fn(&mut S) -> Vec<F>,
    ) -> Result<Self, Error>
    where
        V: IOPVerifier<MT, S, F>,
        S: CryptographicSponge,
        L: LDT<P, F, S>,
        P: IOPProver<MT, S, F, L>,
    {
        // create a BCS transcript
        let mut transcript = Transcript::new(sponge, hash_params);
        // run prover code, using transcript as a simulated verifier
        // This is not a subprotocol, so we use root namespace (/).

        transcript = P::prove(
            prover_initial_state,
            &ROOT_NAMESPACE,
            transcript,
            prover_parameter,
        );
        // perform LDT proof
        let mut low_degree_oracles_ref = Vec::new();
        for msg in &mut transcript.prover_message_oracles {
            match msg {
                ProverMessagesInRound::ReedSolomonCode {
                    degree_bound,
                    oracle,
                    ..
                } => {
                    low_degree_oracles_ref.push((*degree_bound, oracle));
                }
                _ => { /*skip*/ }
            }
        }

        // When proving LDT using IOP (like FRI), the codewords oracle will be queried, and query responses
        // will be stored. Any oracle that not in transcript will be stored in `ldt_proof` in succinct form.
        let ldt_proof = L::prove(ldt_params, &mut transcript.sponge, &low_degree_oracles_ref)?;

        // extract things from transcript
        let mut sponge = transcript.sponge;
        let mut prover_message_oracles = transcript.prover_message_oracles;
        let mut previous_verifier_messages = transcript.verifier_messages;
        let bookkeeper = transcript.bookkeeper;

        // run verifier code (we ignore verifier output)
        V::query_and_decision(
            &ROOT_NAMESPACE,
            verifier_parameter,
            &mut sponge,
            &mut prover_message_oracles,
            &mut previous_verifier_messages,
            &bookkeeper,
        )?;

        // Now all queries are complete. We can convert oracle to succinct oracle so that the oracle
        // will only contain part of messages that will can be queried.
        let succinct_prover_message_oracles: Vec<_> = prover_message_oracles
            .into_iter()
            .map(|x| x.into_succinct())
            .collect();

        // compute final hash
        // TODO: may not needed
        let final_hash = final_hasher(&mut sponge);

        Ok(Self {
            prover_messages: succinct_prover_message_oracles,
            ldt_prover_messages: ...,
        })
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
