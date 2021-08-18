use crate::bcs::message::SuccinctRoundOracle;
use crate::bcs::transcript::{Transcript, ROOT_NAMESPACE};
use crate::bcs::MTHashParameters;
use crate::iop::prover::IOPProver;
use crate::iop::verifier::IOPVerifier;
use crate::ldt_trait::{NoLDT, LDT};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_crypto_primitives::Path;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

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
    pub prover_iop_messages_by_round: Vec<SuccinctRoundOracle<F>>,
    // pub prover_iop_messages_by_round: Vec<SuccinctRoundOracle<F>>,
    // /// Extra Prover messages used for LDT. If the prover is not RS-IOP, this vector should be empty.
    // pub ldt_prover_iop_messages_by_round: Vec<SuccinctRoundOracle<F>>,

    // BCS data below: maybe combine
    /// Merkle tree roots for all prover messages (including main prover and ldt prover).
    pub prover_messages_mt_root: Vec<Option<MT::InnerDigest>>,
    /// Merkle tree paths for queried prover messages in main protocol.
    /// `prover_messages_mt_path[i][j]` is the path for jth query at ith round of prover message.
    pub prover_oracles_mt_path: Vec<Vec<Path<MT>>>,
}

impl<MT, F> BCSProof<MT, F>
where
    MT: MTConfig<Leaf = [F]>,
    F: PrimeField + Absorb,
    MT::InnerDigest: Absorb,
{
    /// Generate proof
    pub fn generate<V, P, L, S>(
        sponge: S,
        public_input: &P::PublicInput,
        private_input: &P::PrivateInput,
        prover_parameter: &P::ProverParameter,
        verifier_parameter: &V::VerifierParameter,
        ldt_params: &L::LDTParameters,
        hash_params: MTHashParameters<MT>,
    ) -> Result<Self, Error>
    where
        V: IOPVerifier<S, F, PublicInput = P::PublicInput>,
        L: LDT<F>,
        P: IOPProver<F>,
        S: CryptographicSponge,
    {
        // create a BCS transcript
        let mut transcript = {
            let ldt_params = ldt_params.clone();
            Transcript::new(sponge, hash_params.clone(), move |degree, domain| {
                L::is_valid_domain(&ldt_params, degree, *domain)
            })
        };

        // run prover code, using transcript to sample verifier message
        // This is not a subprotocol, so we use root namespace (/).
        P::prove(
            &ROOT_NAMESPACE,
            &mut P::initial_state(public_input, private_input),
            &mut transcript,
            prover_parameter,
        )?;

        // sanity check: pending message should be None
        debug_assert!(
            !transcript.is_pending_message_available(),
            "Sanity check failed: pending message not submitted."
        );

        // perform LDT to enforce degree bound on low-degree oracles
        let mut ldt_transcript = Transcript::new(transcript.sponge, hash_params, |_, _| true);
        {
            // TODO: verify the domain here
            let codeword_oracles_ref = transcript
                .prover_message_oracles
                .iter()
                .map(|msg| &msg.reed_solomon_codes);

            // Given the entire codewords of all low-degree messages in the protocol,
            // run the ldt prover to generate LDT prover messages.
            L::prove(ldt_params, codeword_oracles_ref, &mut ldt_transcript)?;
        }

        debug_assert!(
            !ldt_transcript.is_pending_message_available(),
            "Sanity check failed: pending message not submitted."
        );

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

        // run LDT verifier code to obtain all queries. We will use this query to generate succinct oracles from message recording oracle.
        {
            L::query_and_decide(
                ldt_params,
                &mut sponge,
                prover_message_oracles.iter_mut().collect(),
                ldt_prover_message_oracles.iter_mut().collect(),
                ldt_verifier_messages.as_slice(),
            )?;
        }

        // run main verifier code to obtain all queries
        {
            V::query_and_decide(
                &ROOT_NAMESPACE,
                verifier_parameter,
                &mut V::initial_state_for_query_and_decision_phase(public_input),
                &mut sponge,
                prover_message_oracles.iter_mut().collect(),
                &verifier_messages,
                &bookkeeper,
            )?;
        }

        let all_message_oracles = || {
            prover_message_oracles
                .iter()
                .chain(ldt_prover_message_oracles.iter())
        };

        // convert oracles to succinct oracle
        let all_succinct_oracles: Vec<_> = all_message_oracles()
            .map(|x| x.get_succinct_oracle())
            .collect();

        let all_queries: Vec<_> = all_message_oracles()
            .map(|msg| msg.queries.clone())
            .collect();

        // generate all merkle tree paths
        debug_assert_eq!(
            merkle_trees.len() + ldt_merkle_trees.len(),
            all_queries.len()
        );
        let all_mt_paths = all_queries
            .iter()
            .zip(merkle_trees.iter().chain(ldt_merkle_trees.iter()))
            .map(|(queries, mt)| {
                queries
                    .iter()
                    .map(|query| {
                        mt.as_ref()
                            .expect("this oracle contains query but has no merkle tree")
                            .generate_proof(*query)
                            .expect("fail to generate mt path")
                    })
                    .collect()
            })
            .collect();

        let all_mt_roots: Vec<_> = merkle_trees
            .iter()
            .chain(ldt_merkle_trees.iter())
            .map(|x| x.as_ref().map(|tree| tree.root()))
            .collect();

        Ok(BCSProof {
            // todo: maybe combine prover and ldt?
            prover_iop_messages_by_round: all_succinct_oracles,
            prover_messages_mt_root: all_mt_roots,
            prover_oracles_mt_path: all_mt_paths,
        })
    }

    /// Generate proof
    /// do it in future: derive verifier param from prover param
    pub fn generate_without_ldt<V, P, S>(
        sponge: S,
        public_input: &P::PublicInput,
        private_input: &P::PrivateInput,
        prover_parameter: &P::ProverParameter,
        verifier_parameter: &V::VerifierParameter,
        hash_params: MTHashParameters<MT>,
    ) -> Result<Self, Error>
    where
        V: IOPVerifier<S, F, PublicInput = P::PublicInput>,
        P: IOPProver<F>,
        S: CryptographicSponge,
    {
        Self::generate::<V, P, NoLDT<F>, _>(
            sponge,
            public_input,
            private_input,
            prover_parameter,
            verifier_parameter,
            &(),
            hash_params,
        )
    }
}
