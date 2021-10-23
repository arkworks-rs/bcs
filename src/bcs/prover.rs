use crate::{
    bcs::{
        transcript::{NameSpace, Transcript},
        MTHashParameters,
    },
    iop::{
        message::{MessagesCollection, SuccinctRoundOracle},
        prover::IOPProverWithNoOracleRefs,
        verifier::IOPVerifierForProver,
        ProverParam,
    },
    ldt::{NoLDT, LDT},
    Error,
};
use ark_crypto_primitives::{merkle_tree::Config as MTConfig, Path};
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Read, SerializationError, Write};
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::vec::Vec;

/// BCSProof contains all prover messages that use succinct oracle, and thus is
/// itself succinct.
#[derive(CanonicalSerialize, CanonicalDeserialize, Derivative)]
#[derivative(Clone(bound = "MT: MTConfig, F: PrimeField"))]
pub struct BCSProof<MT, F>
where
    MT: MTConfig,
    F: PrimeField,
    MT::InnerDigest: Absorb,
{
    /// Messages sent by prover in commit phase. Each item in the vector
    /// represents a list of message oracles (reed solomon codes go first)
    /// with same length. The length constraints do not hold for short messages
    /// (IP message). All non-IP messages in the same prover round share the
    /// same merkle tree. Each merkle tree leaf is a vector which each
    /// element correspond to the same coset of different oracles.
    pub prover_iop_messages_by_round: Vec<SuccinctRoundOracle<F>>,

    // BCS data below: maybe combine
    /// Merkle tree roots for all prover messages (including main prover and ldt
    /// prover).
    pub prover_messages_mt_root: Vec<Option<MT::InnerDigest>>,
    /// Merkle tree paths for queried prover messages in main protocol.
    /// `prover_messages_mt_path[i][j]` is the path for jth query at ith round
    /// of prover message.
    pub prover_oracles_mt_path: Vec<Vec<Path<MT>>>,
}

impl<MT, F> BCSProof<MT, F>
where
    MT: MTConfig<Leaf = [F]>,
    F: PrimeField + Absorb,
    MT::InnerDigest: Absorb,
{
    /// Generate proof
    /// This function requires that IOPProver and IOPVerifier is not a
    /// subprotocol, which essentially means that `OracleRefs` for both agent
    /// needs to be `()`.
    pub fn generate<V, P, L, S>(
        sponge: S,
        public_input: &P::PublicInput,
        private_input: &P::PrivateInput,
        prover_parameter: &P::ProverParameter,
        ldt_params: &L::LDTParameters,
        hash_params: MTHashParameters<MT>,
    ) -> Result<Self, Error>
    where
        L: LDT<F>,
        P: IOPProverWithNoOracleRefs<F>,
        V: IOPVerifierForProver<S, F, P>,
        S: CryptographicSponge,
    {
        let verifier_parameter = prover_parameter.to_verifier_param();

        // create a BCS transcript
        let mut transcript = {
            Transcript::new(
                sponge,
                hash_params.clone(),
                move |degree| L::ldt_info(&ldt_params, degree),
                iop_trace!("BCS Proof Generation"),
            )
        };

        let root_namespace = NameSpace::root(iop_trace!("BCS Proof Generation: Commit Phase"));

        // run prover code, using transcript to sample verifier message
        // This is not a subprotocol, so we use root namespace (/).
        P::prove(
            root_namespace,
            &(),
            public_input,
            private_input,
            &mut transcript,
            prover_parameter,
        )?;

        // sanity check: pending message should be None
        debug_assert!(
            !transcript.is_pending_message_available(),
            "Sanity check failed: pending message not submitted."
        );

        // perform LDT to enforce degree bound on low-degree oracles

        let ldt_namespace = transcript.new_namespace(root_namespace, iop_trace!("LDT"));
        let codewords = transcript.bookkeeper.dump_all_prover_messages_in_order();

        L::prove(ldt_namespace, ldt_params, &mut transcript, &codewords)?;

        debug_assert!(
            !transcript.is_pending_message_available(),
            "Sanity check failed: pending message not submitted."
        );

        // extract things from main transcript
        let mut sponge = transcript.sponge;

        let mut transcript_messages = MessagesCollection::new(
            transcript.prover_message_oracles,
            transcript.verifier_messages,
            transcript.bookkeeper,
        );

        // run LDT verifier code to obtain all queries. We will use this query to
        // generate succinct oracles from message recording oracle.

        L::query_and_decide(
            ldt_namespace,
            &ldt_params,
            &mut sponge,
            &codewords,
            &mut transcript_messages,
        )?;

        // run main verifier code to obtain all queries

        V::query_and_decide(
            NameSpace::root(iop_trace!("BCS Proof Generation: Query and Decision Phase")),
            &verifier_parameter,
            public_input,
            &(),
            &mut sponge,
            &mut transcript_messages,
        )?;

        // convert oracles to succinct oracle
        let all_succinct_oracles: Vec<_> = transcript_messages
            .prover_messages
            .iter()
            .map(|x| x.get_succinct_oracle())
            .collect();

        let all_queries: Vec<_> = transcript_messages
            .prover_messages
            .iter()
            .map(|msg| msg.queried_coset_index.clone())
            .collect();

        let merkle_trees = transcript.merkle_tree_for_each_round;

        // generate all merkle tree paths
        debug_assert_eq!(merkle_trees.len(), all_queries.len());
        let all_mt_paths = all_queries
            .iter()
            .zip(merkle_trees.iter())
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
            .map(|x| x.as_ref().map(|tree| tree.root()))
            .collect();

        Ok(BCSProof {
            prover_iop_messages_by_round: all_succinct_oracles,
            prover_messages_mt_root: all_mt_roots,
            prover_oracles_mt_path: all_mt_paths,
        })
    }

    /// Generate proof without LDT. Panic if prover tries to send lower degree
    /// oracles.
    pub fn generate_with_ldt_disabled<V, P, S>(
        sponge: S,
        public_input: &P::PublicInput,
        private_input: &P::PrivateInput,
        prover_parameter: &P::ProverParameter,
        hash_params: MTHashParameters<MT>,
    ) -> Result<Self, Error>
    where
        V: IOPVerifierForProver<S, F, P>,
        P: IOPProverWithNoOracleRefs<F>,
        S: CryptographicSponge,
    {
        Self::generate::<V, P, NoLDT<F>, _>(
            sponge,
            public_input,
            private_input,
            prover_parameter,
            &None,
            hash_params,
        )
    }

    /// Generate proof without LDT. Prover send low degree oracles using
    /// `ldt_codeword_domain` and `ldt_codeword_localization_parameter`.
    pub fn generate_with_dummy_ldt<V, P, S>(
        sponge: S,
        public_input: &P::PublicInput,
        private_input: &P::PrivateInput,
        prover_parameter: &P::ProverParameter,
        hash_params: MTHashParameters<MT>,
        ldt_codeword_domain: Radix2CosetDomain<F>,
        ldt_codeword_localization_parameter: usize,
    ) -> Result<Self, Error>
    where
        V: IOPVerifierForProver<S, F, P>,
        P: IOPProverWithNoOracleRefs<F>,
        S: CryptographicSponge,
    {
        Self::generate::<V, P, NoLDT<F>, _>(
            sponge,
            public_input,
            private_input,
            prover_parameter,
            &Some((ldt_codeword_domain, ldt_codeword_localization_parameter)),
            hash_params,
        )
    }
}
