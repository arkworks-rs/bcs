use crate::bcs::message::{RecordingRoundOracle, SuccinctRoundOracle};
use crate::bcs::transcript::{Transcript, ROOT_NAMESPACE};
use crate::bcs::MTHashParameters;
use crate::iop::prover::IOPProver;
use crate::iop::verifier::IOPVerifier;
use crate::ldt_trait::{NoLDT, LDT};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_crypto_primitives::{MerkleTree, Path};
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
    /// Extra Prover messages used for LDT. If the prover is not RS-IOP, this vector should be empty.
    pub ldt_prover_iop_messages_by_round: Vec<SuccinctRoundOracle<F>>,

    // BCS data below: maybe combine

    /// Merkle tree root for prover messages in main protocol.
    pub prover_messages_mt_root: Vec<Option<MT::InnerDigest>>,
    /// Merkle tree root for extra prover messages used for LDT. If the prover is not RS-IOP, this vector should be empty.
    pub ldt_prover_messages_mt_root: Vec<Option<MT::InnerDigest>>, // TODO: making this combined

    /// Merkle tree paths for queried prover messages in main protocol.
    /// `prover_messages_mt_path[i][j]` is the path for jth query at ith round of prover message.
    pub prover_oracles_mt_path: Vec<Vec<Path<MT>>>,
    /// Merkle tree paths for queried LDT prover messages in main protocol.
    /// `ldt_messages_mt_path[i][j]` is the path for jth query at ith round of ldt prover message.
    pub ldt_prover_oracles_mt_path: Vec<Vec<Path<MT>>>,
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
        let mut transcript = Transcript::new(sponge, hash_params.clone());

        // run prover code, using transcript to sample verifier message
        // This is not a subprotocol, so we use root namespace (/).
        P::prove(
            &ROOT_NAMESPACE,
            &mut P::initial_state(public_input, private_input),
            &mut transcript,
            prover_parameter,
        );

        // sanity check: pending message should be None
        debug_assert!(
            !transcript.is_pending_message_available(),
            "Sanity check failed: pending message not submitted."
        );

        // perform LDT to enforce degree bound on low-degree oracles
        let mut ldt_transcript = Transcript::new(transcript.sponge, hash_params);
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

        // convert oracles to succinct oracle
        let succinct_prover_message_oracles =
            Self::batch_to_succinct(&prover_message_oracles, false);
        let succinct_ldt_prover_message_oracles =
            Self::batch_to_succinct(&ldt_prover_message_oracles, false);

        let main_queries: Vec<_> = prover_message_oracles.into_iter().map(|msg|msg.queries).collect();
        let ldt_queries: Vec<_> = ldt_prover_message_oracles.into_iter().map(|msg|msg.queries).collect();

        // compute all authentication paths
        let prover_message_paths =
            Self::generate_all_paths(&main_queries, merkle_trees.as_slice());
        let ldt_prover_message_paths =
            Self::generate_all_paths(&ldt_queries, &ldt_merkle_trees);

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
            // todo: maybe combine prover and ldt?
            prover_iop_messages_by_round: succinct_prover_message_oracles,
            prover_messages_mt_root: prover_mt_root,
            prover_oracles_mt_path: prover_message_paths,
            ldt_prover_iop_messages_by_round: succinct_ldt_prover_message_oracles,
            ldt_prover_messages_mt_root: ldt_prover_mt_root,
            ldt_prover_oracles_mt_path: ldt_prover_message_paths,
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

    fn batch_to_succinct(
        oracles: &[RecordingRoundOracle<F>],
        assert_no_ldt: bool,
    ) -> Vec<SuccinctRoundOracle<F>> {
        oracles
            .iter()
            .map(|x| {
                if assert_no_ldt {
                    assert!(x.reed_solomon_codes.is_empty(), "low degree codes is used")
                };
                x.get_succinct_oracle()
            })
            .collect()
    }

    fn generate_all_paths(
        queries: &[Vec<usize>],
        mt: &[Option<MerkleTree<MT>>],
    ) -> Vec<Vec<Path<MT>>> {
        debug_assert_eq!(mt.len(), queries.len());
        queries.iter()
            .zip(mt.iter())
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
            .collect()
    }
}
