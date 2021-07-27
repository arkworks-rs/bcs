use crate::bcs::message::{ProverMessage, SuccinctOracle};
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
    bound = "MT: MTConfig, F: PrimeField,S: CryptographicSponge, L: LDT<MT, F, S>"
))]
pub struct BCSProof<MT, F, S, L>
where
    MT: MTConfig,
    F: PrimeField,
    S: CryptographicSponge,
    L: LDT<MT, F, S>,
    MT::InnerDigest: Absorb,
{
    /// Prover succinct oracle message
    pub prover_message: Vec<ProverMessage<MT, F, SuccinctOracle<MT, F>>>,
    /// Proof of low-degree bound
    ldt_proof: L::LDTProof,
    /// Final hash
    final_hash: Vec<F>,
}

impl<MT, F, S, L> BCSProof<MT, F, S, L>
where
    MT: MTConfig<Leaf = F>,
    F: PrimeField,
    S: CryptographicSponge,
    L: LDT<MT, F, S>,
    MT::InnerDigest: Absorb,
{
    /// Generate proof
    pub fn generate<V, P>(
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
                ProverMessage::ReedSolomonCode {
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
        let final_hash = final_hasher(&mut sponge);

        Ok(Self {
            prover_message: succinct_prover_message_oracles,
            ldt_proof,
            final_hash,
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
