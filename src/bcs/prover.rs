use crate::bcs::message::{ProverMessagesInRound, SuccinctOracle};
use crate::bcs::transcript::{Transcript, ROOT_NAMESPACE};
use crate::bcs::MTHashParameters;
use crate::iop::prover::IOPProver;
use crate::iop::verifier::IOPVerifier;
use crate::ldt_trait::LDT;
use crate::Error;
use ark_crypto_primitives::merkle_tree::{Config as MTConfig, Config};
use ark_crypto_primitives::{MerkleTree, Path};
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};
use std::collections::{BTreeMap, BTreeSet};

/// BCSProof contains all prover messages that use succinct oracle, and thus is itself succinct.
#[derive(Derivative)]
#[derivative(Clone(bound = "MT: MTConfig, F: PrimeField"))]
pub struct BCSProof<MT, F>
where
    MT: MTConfig,
    F: PrimeField,
    MT::InnerDigest: Absorb,
{
    /// Messages sent by prover in commit phase. Each item in the vector represents a list of
    /// message oracles with same length. The length constraints do not hold for short messages (IP message).
    /// All non-IP messages in the same prover round should share the same merkle tree. Each merkle tree leaf is
    /// a vector which each element correspond to the same location of different oracles.
    ///
    /// Prover succinct oracle message. If the user uses RSIOP, the oracles in last `n` rounds will be used for LDT with
    /// `n` queries.
    pub prover_messages: Vec<ProverMessagesInRound<F, SuccinctOracle<F>>>,
    /// Extra Prover messages used for LDT. If the prover is not RS-IOP, this vector should be empty.
    pub ldt_prover_messages: Vec<ProverMessagesInRound<F, SuccinctOracle<F>>>,

    /// Merkle tree root for prover messages in main protocol.
    pub prover_messages_mt_root: Vec<Option<MT::InnerDigest>>,
    /// Merkle tree root for extra prover messages used for LDT. If the prover is not RS-IOP, this vector should be empty.
    pub ldt_prover_messages_mt_root: Vec<Option<MT::InnerDigest>>,

    /// Merkle tree paths for queried prover messages in main protocol.
    pub prover_messages_mt_path: Vec<BTreeMap<usize, Path<MT>>>,
    /// Merkle tree paths for queried LDT prover messages in main protocol.
    pub ldt_messages_mt_path: Vec<BTreeMap<usize, Path<MT>>>,
}

impl<MT, F> BCSProof<MT, F>
where
    MT: MTConfig<Leaf = Vec<F>>,
    F: PrimeField + Absorb,
    MT::InnerDigest: Absorb,
{
    /// Generate proof
    pub fn generate<V, P, L, S>(
        sponge: S,
        prover_initial_state: &mut P::ProverState,
        prover_parameter: &P::ProverParameter,
        verifier_parameter: &V::VerifierParameter,
        ldt_params: &L::LDTParameters,
        hash_params: MTHashParameters<MT>,
    ) -> Result<Self, Error>
    where
        V: IOPVerifier<S, F>,
        L: LDT<F>,
        P: IOPProver<F>,
        S: CryptographicSponge,
    {
        // create a BCS transcript
        let mut transcript = Transcript::new(sponge, hash_params.clone());

        // run prover code, using transcript as a simulated verifier
        // This is not a subprotocol, so we use root namespace (/).
        P::prove(
            prover_initial_state,
            &ROOT_NAMESPACE,
            &mut transcript,
            prover_parameter,
        );

        // perform LDT proof
        let mut ldt_transcript = Transcript::new(transcript.sponge, hash_params);
        {
            let low_degree_messages_ref: Vec<_> = transcript
                .prover_message_oracles
                .iter()
                .map(|msg| {
                    msg.reed_solomon_codes
                        .iter()
                        .map(|(oracle, degree)| (*degree, oracle.leaves.as_slice()))
                })
                .flatten()
                .collect();

            // Given the entire codewords of all low-degree messages in the protocol,
            // run the ldt prover to generate LDT prover messages.
            L::prove(ldt_params, &low_degree_messages_ref, &mut ldt_transcript)?;
        }

        // extract things from main transcript
        let mut sponge = ldt_transcript.sponge;
        let mut prover_message_oracles = transcript.prover_message_oracles;
        let merkle_trees = transcript.merkle_tree_for_each_round;
        let verifier_messages = transcript.verifier_messages;
        let bookkeeper = transcript.bookkeeper;

        // extract things from LDT transcript
        let mut ldt_prover_message_oracles = ldt_transcript.prover_message_oracles;
        let ldt_merkle_trees = ldt_transcript.merkle_tree_for_each_round;
        let ldt_verifier_messages = ldt_transcript.verifier_messages;

        {
            // get the mutable codeword oracle reference for LDT
            let low_degree_oracle_ref: Vec<_> = prover_message_oracles
                .iter_mut()
                .map(|msg| msg.reed_solomon_codes.iter_mut().map(|(oracle, _)| oracle))
                .flatten()
                .collect();

            // run LDT verifier code
            let ldt_prover_message_oracles_ref: Vec<_> =
                ldt_prover_message_oracles.iter_mut().collect();
            L::query_and_decide(
                ldt_params,
                &mut sponge,
                &low_degree_oracle_ref,
                &ldt_prover_message_oracles_ref,
                ldt_verifier_messages.as_slice(),
            )?;
        }

        // run verifier code (we ignore verifier output)
        {
            let prover_message_oracles_ref: Vec<_> = prover_message_oracles.iter_mut().collect();
            V::query_and_decide(
                &ROOT_NAMESPACE,
                verifier_parameter,
                &mut sponge,
                &prover_message_oracles_ref,
                &verifier_messages,
                &bookkeeper,
            )?;
        }

        // convert oracles to succint oracle
        let (succinct_prover_message_oracles, queried_indices): (Vec<_>, Vec<_>) =
            prover_message_oracles
                .into_iter()
                .map(|x| x.into_succinct())
                .unzip();
        let (succinct_ldt_prover_message_oracles, ldt_query_indices): (Vec<_>, Vec<_>) =
            ldt_prover_message_oracles
                .into_iter()
                .map(|x| x.into_succinct())
                .unzip();

        // compute all authentication paths
        let prover_message_paths = generate_mt_paths(queried_indices, &merkle_trees);
        let ldt_prover_message_paths = generate_mt_paths(ldt_query_indices, &ldt_merkle_trees);

        // compute all merkle tree roots
        let prover_mt_root: Vec<_> = merkle_trees
            .iter()
            .map(|x| x.as_ref().map(|tree| tree.root()))
            .collect();
        let ldt_prover_mt_root: Vec<_> = ldt_merkle_trees
            .iter()
            .map(|x| x.as_ref().map(|tree| tree.root()))
            .collect();
        Ok(BCSProof {
            prover_messages: succinct_prover_message_oracles,
            prover_messages_mt_root: prover_mt_root,
            prover_messages_mt_path: prover_message_paths,
            ldt_prover_messages: succinct_ldt_prover_message_oracles,
            ldt_prover_messages_mt_root: ldt_prover_mt_root,
            ldt_messages_mt_path: ldt_prover_message_paths,
        })
    }
}

fn generate_mt_paths<P: Config>(
    queried_indices: Vec<BTreeSet<usize>>,
    merkle_trees: &[Option<MerkleTree<P>>],
) -> Vec<BTreeMap<usize, Path<P>>> {
    queried_indices
        .into_iter()
        .map(|query| {
            let paths_curr_round: BTreeMap<_, _> = query
                .into_iter()
                .map(|index| {
                    (
                        index,
                        merkle_trees[index]
                            .as_ref()
                            .expect("merkle tree for this round should not be empty")
                            .generate_proof(index)
                            .expect("unable to generate merkle tree proof"),
                    )
                })
                .collect();
            paths_curr_round
        })
        .collect()
}

fn le_bits_to_usize(bits: &[bool]) -> usize {
    let mut result = 0;
    bits.iter().for_each(|&x| {
        result <<= 1;
        result |= x as usize;
    });
    result
}
