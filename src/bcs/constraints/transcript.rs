use crate::{
    bcs::{
        constraints::proof::BCSProofVar,
        transcript::{MessageBookkeeper, NameSpace},
    },
    iop::{
        constraints::message::{SuccinctRoundOracleVar, VerifierMessageVar},
        message::{MsgRoundRef, ProverRoundMessageInfo},
    },
    tracer::TraceInfo,
};
use ark_crypto_primitives::merkle_tree::{constraints::ConfigGadget, Config};
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::SynthesisError;
use ark_sponge::{
    constraints::{AbsorbGadget, CryptographicSpongeVar, SpongeWithGadget},
    Absorb,
};
use ark_std::{boxed::Box, mem::take, vec::Vec};
use tracing::info;

/// R1CS Variable for simulation transcript used by verifier.
pub struct SimulationTranscriptVar<'a, F, MT, MTG, S>
where
    F: PrimeField + Absorb,
    MT: Config,
    MTG: ConfigGadget<MT, F, Leaf = [FpVar<F>]>,
    S: SpongeWithGadget<F>,
    MT::InnerDigest: Absorb,
    F: Absorb,
    MTG::InnerDigest: AbsorbGadget<F>,
{
    pub(crate) prover_messages_info: Vec<ProverRoundMessageInfo>,
    prover_mt_roots: &'a [Option<MTG::InnerDigest>],
    prover_short_messages: Vec<&'a Vec<Vec<FpVar<F>>>>,
    pub(crate) sponge: S::Var,
    pub(crate) current_prover_round: usize,
    pub(crate) reconstructed_verifier_messages: Vec<Vec<VerifierMessageVar<F>>>,

    pending_verifier_messages: Vec<VerifierMessageVar<F>>,
    pub(crate) bookkeeper: MessageBookkeeper,
    ldt_info: Box<dyn Fn(usize) -> (Radix2CosetDomain<F>, usize) + 'a>,
}

impl<'a, F, MT, MTG, S> SimulationTranscriptVar<'a, F, MT, MTG, S>
where
    F: PrimeField + Absorb,
    MT: Config,
    MTG: ConfigGadget<MT, F, Leaf = [FpVar<F>]>,
    S: SpongeWithGadget<F>,
    MT::InnerDigest: Absorb,
    F: Absorb,
    MTG::InnerDigest: AbsorbGadget<F>,
{
    pub(crate) fn new_transcript(
        bcs_proof: &'a BCSProofVar<MT, MTG, F>,
        sponge: S::Var,
        ldt_info: impl Fn(usize) -> (Radix2CosetDomain<F>, usize) + 'a,
        trace: TraceInfo,
    ) -> Self {
        Self::new_transcript_with_offset(bcs_proof, 0, sponge, ldt_info, trace)
    }

    pub(crate) fn new_transcript_with_offset(
        bcs_proof: &'a BCSProofVar<MT, MTG, F>,
        round_offset: usize,
        sponge: S::Var,
        ldt_info: impl Fn(usize) -> (Radix2CosetDomain<F>, usize) + 'a,
        trace: TraceInfo,
    ) -> Self {
        let prover_short_messages: Vec<_> = bcs_proof.prover_iop_messages_by_round[round_offset..]
            .iter()
            .map(|msg| &msg.short_messages)
            .collect();
        let prover_messages_info: Vec<_> = bcs_proof.prover_iop_messages_by_round[round_offset..]
            .iter()
            .map(|msg| msg.info.clone())
            .collect();
        Self {
            prover_short_messages,
            prover_messages_info,
            prover_mt_roots: &bcs_proof.prover_messages_mt_root[round_offset..],
            sponge,
            current_prover_round: 0,
            bookkeeper: MessageBookkeeper::new(trace),
            reconstructed_verifier_messages: Vec::new(),
            pending_verifier_messages: Vec::new(),
            ldt_info: Box::new(ldt_info),
        }
    }

    /// Create a new namespace in this transcript
    pub fn new_namespace(&mut self, current_namespace: NameSpace, trace: TraceInfo) -> NameSpace {
        self.bookkeeper.new_namespace(trace, current_namespace.id)
    }

    /// Create a simulation transcript from a list of prover messages, its
    /// corresponding merkle tree, sponge variable, and LDT information,
    ///
    /// `ldt_info` may panic if `NoLDT` is used.
    pub fn from_prover_messages(
        prover_iop_messages_by_round: &'a [SuccinctRoundOracleVar<F>],
        prover_iop_messages_mt_roots_by_round: &'a [Option<MTG::InnerDigest>],
        sponge_var: S::Var,
        ldt_info: impl Fn(usize) -> (Radix2CosetDomain<F>, usize) + 'a,
        trace: TraceInfo,
    ) -> Self {
        let prover_short_messages = prover_iop_messages_by_round
            .iter()
            .map(|msg| &msg.short_messages)
            .collect::<Vec<_>>();
        let prover_messages_info = prover_iop_messages_by_round
            .iter()
            .map(|msg| msg.get_view().get_info().clone())
            .collect();
        Self {
            prover_short_messages,
            prover_messages_info,
            prover_mt_roots: prover_iop_messages_mt_roots_by_round,
            sponge: sponge_var,
            current_prover_round: 0,
            bookkeeper: MessageBookkeeper::new(trace),
            reconstructed_verifier_messages: Vec::new(),
            pending_verifier_messages: Vec::new(),
            ldt_info: Box::new(ldt_info),
        }
    }

    /// Number of submitted rounds in the transcript
    pub fn num_prover_rounds_submitted(&self) -> usize {
        self.current_prover_round
    }

    /// Receive prover's current round messages, which can possibly contain
    /// multiple oracles with same size. This function will absorb the
    /// merkle tree root and short messages (if any).
    ///
    /// If the function contains low-degree oracle, localization parameter in
    /// `expected_message_info` will be ignored, because localization
    /// parameter is managed by LDT. # Panic
    /// This function will panic is prover message structure contained in proof
    /// is not consistent with `expected_message_structure`.
    #[tracing::instrument(skip(self, ns, expected_message_info, tracer))]
    pub fn receive_prover_current_round(
        &mut self,
        ns: NameSpace,
        mut expected_message_info: ProverRoundMessageInfo,
        tracer: TraceInfo,
    ) -> Result<MsgRoundRef, SynthesisError> {
        info!("{}", tracer.description());
        if expected_message_info.reed_solomon_code_degree_bound.len() > 0 {
            // LDT is used, so replace its localization parameter with the one given by LDT
            let localization_parameters_from_ldt = expected_message_info
                .reed_solomon_code_degree_bound
                .iter()
                .map(|&degree| self.ldt_info(degree).1)
                .collect::<Vec<_>>();
            // check all localization are equal, for consistency
            localization_parameters_from_ldt.iter().for_each(|&p| {
                assert_eq!(
                    p, localization_parameters_from_ldt[0],
                    "different localization parameters in one round is not allowed"
                )
            });
            expected_message_info.localization_parameter = localization_parameters_from_ldt[0]
        }

        let index = self.current_prover_round;
        self.current_prover_round += 1;

        assert_eq!(
            &expected_message_info, &self.prover_messages_info[index],
            "prover message is not what verifier want at current round"
        );

        // absorb merkle tree root, if any
        self.sponge.absorb(&self.prover_mt_roots[index])?;

        // absorb short messages for this round, if any
        self.prover_short_messages[index]
            .iter()
            .try_for_each(|msg| self.sponge.absorb(msg))?;

        Ok(self.attach_latest_prover_round_to_namespace(ns, tracer))
    }

    /// Submit all verification messages in this round
    #[tracing::instrument(skip(self, namespace, tracer))]
    pub fn submit_verifier_current_round(
        &mut self,
        namespace: NameSpace,
        tracer: TraceInfo,
    ) -> MsgRoundRef {
        info!("{}", tracer);
        let pending_message = take(&mut self.pending_verifier_messages);
        self.reconstructed_verifier_messages.push(pending_message);
        self.attach_latest_verifier_round_to_namespace(namespace, tracer)
    }

    /// Squeeze sampled verifier message as field elements. The squeezed
    /// elements is attached to pending messages, and need to be submitted
    /// through `submit_verifier_current_round`. Submitted messages will be
    /// stored in transcript and will be later given to verifier in query
    /// and decision phase.
    ///
    /// **Note**: Since we are not running the actual prover code, verifier
    /// message is not used `reconstructed_verifer_messages`, so this
    /// function returns nothing. TODO: current limitation: sponge
    /// constraints does not support squeeze native elements with size
    pub fn squeeze_verifier_field_elements(
        &mut self,
        num_elements: usize,
    ) -> Result<(), SynthesisError> {
        let msg = self.sponge.squeeze_field_elements(num_elements)?;
        self.pending_verifier_messages
            .push(VerifierMessageVar::FieldElements(msg));
        Ok(())
    }

    /// Squeeze sampled verifier message as bytes. The squeezed bytes is
    /// attached to pending messages, and need to be submitted through
    /// `submit_verifier_current_round`. Submitted messages will be stored
    /// in transcript and will be later given to verifier in query and
    /// decision phase.
    ///
    /// **Note**: Since we are not running the actual prover code, verifier
    /// message is not used `reconstructed_verifer_messages`, so this
    /// function returns nothing.
    pub fn squeeze_verifier_field_bytes(&mut self, num_bytes: usize) -> Result<(), SynthesisError> {
        let msg = self.sponge.squeeze_bytes(num_bytes)?;
        self.pending_verifier_messages
            .push(VerifierMessageVar::Bytes(msg));
        Ok(())
    }

    /// Squeeze sampled verifier message as bytes. The squeezed bytes is
    /// attached to pending messages, and need to be submitted through
    /// `submit_verifier_current_round`. Submitted messages will be stored
    /// in transcript and will be later given to verifier in query and
    /// decision phase.
    ///
    /// **Note**: Since we are not running the actual prover code, verifier
    /// message is not used `reconstructed_verifer_messages`, so this
    /// function returns nothing.
    pub fn squeeze_verifier_field_bits(&mut self, num_bits: usize) -> Result<(), SynthesisError> {
        let msg = self.sponge.squeeze_bits(num_bits)?;
        self.pending_verifier_messages
            .push(VerifierMessageVar::Bits(msg));
        Ok(())
    }

    /// Returns if there is a verifier message for the transcript.
    pub fn is_pending_message_available(&self) -> bool {
        !self.pending_verifier_messages.is_empty()
    }

    fn attach_latest_prover_round_to_namespace(
        &mut self,
        namespace: NameSpace,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        // add verifier message index to namespace
        let index = self.current_prover_round - 1;
        self.bookkeeper
            .attach_prover_round_to_namespace(namespace, index, trace)
    }

    fn attach_latest_verifier_round_to_namespace(
        &mut self,
        namespace: NameSpace,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        // add verifier message index to namespace
        let index = self.reconstructed_verifier_messages.len() - 1;
        self.bookkeeper
            .attach_verifier_round_to_namespace(namespace, index, trace)
    }

    fn ldt_info(&self, degree: usize) -> (Radix2CosetDomain<F>, usize) {
        (self.ldt_info)(degree)
    }
}

#[cfg(any(feature = "test_utils", test))]
/// Utilities for testing if `register_iop_structure_var` is correct
pub mod test_utils {
    use crate::{
        bcs::{
            constraints::transcript::SimulationTranscriptVar,
            transcript::{NameSpace, Transcript},
            MTHashParameters,
        },
        iop::{
            constraints::{message::SuccinctRoundOracleVar, IOPVerifierWithGadget},
            prover::IOPProverWithNoOracleRefs,
        },
        ldt::constraints::LDTWithGadget,
    };
    use ark_crypto_primitives::merkle_tree::{constraints::ConfigGadget, Config};
    use ark_ff::PrimeField;
    use ark_r1cs_std::{alloc::AllocVar, fields::fp::FpVar, R1CSVar};
    use ark_sponge::{
        constraints::{AbsorbGadget, CryptographicSpongeVar, SpongeWithGadget},
        Absorb,
    };
    use ark_std::{collections::BTreeSet, vec::Vec};

    /// Check if simulation transcript generated by `register_iop_structure`
    /// is consistent with prover transcript
    pub fn check_transcript_var_consistency<MT, MTG, S, F>(
        prover_transcript: &Transcript<MT, S, F>,
        verifier_transcript: &SimulationTranscriptVar<F, MT, MTG, S>,
    ) where
        MT: Config<Leaf = [F]>,
        MTG: ConfigGadget<MT, F, Leaf = [FpVar<F>]>,
        S: SpongeWithGadget<F>,
        F: PrimeField + Absorb,
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<F>,
    {
        // check namespace consistency
        assert_eq!(
            verifier_transcript
                .bookkeeper
                .messages_store
                .keys()
                .collect::<BTreeSet<_>>(),
            prover_transcript
                .bookkeeper
                .messages_store
                .keys()
                .collect::<BTreeSet<_>>(),
            "inconsistent namespace used"
        );
        // check for each namespace
        verifier_transcript
            .bookkeeper
            .messages_store
            .keys()
            .for_each(|key| {
                let namespace_diag = ark_std::format!(
                    "Prover transcript defines this namespace as {}\n\
             Verifier defines this namespace as {}\n",
                    prover_transcript
                        .bookkeeper
                        .ns_details
                        .get(key)
                        .unwrap()
                        .trace,
                    verifier_transcript
                        .bookkeeper
                        .ns_details
                        .get(key)
                        .unwrap()
                        .trace
                );
                let indices_in_current_namespace_pt =
                    &prover_transcript.bookkeeper.messages_store[key];
                let indices_in_current_namespace_vt =
                    &verifier_transcript.bookkeeper.messages_store[key];

                (0..indices_in_current_namespace_pt.verifier_message_refs.len()).for_each(|i| {
                    let verifier_message_trace_pt =
                        &indices_in_current_namespace_pt.verifier_message_refs[i].trace;
                    let verifier_message_trace_vt =
                        &indices_in_current_namespace_vt.verifier_message_refs[i].trace;
                    // verifier message gained by prover transcript
                    let verifier_message_pt = &prover_transcript.verifier_messages
                        [indices_in_current_namespace_pt.verifier_message_refs[i].index];
                    // verifier message gained by verifier simulation transcript
                    let verifier_message_vt = &verifier_transcript.reconstructed_verifier_messages
                        [indices_in_current_namespace_vt.verifier_message_refs[i].index]
                        .value()
                        .unwrap();
                    assert_eq!(
                        verifier_message_pt, verifier_message_vt,
                        "Inconsistent verifier round #{}.\n\
             Prover transcript message trace: {}\n\
             Verifier transcript message trace: {}\n\
             {}
             ",
                        i, verifier_message_trace_pt, verifier_message_trace_vt, namespace_diag
                    );
                });
            })
    }

    /// Check if simulation transcript variable filled by the verifier
    /// constraints is consistent with prover transcript
    pub fn check_commit_phase_correctness_var<
        F: PrimeField + Absorb,
        S: SpongeWithGadget<F>,
        MT: Config<Leaf = [F]>,
        MTG: ConfigGadget<MT, F, Leaf = [FpVar<F>]>,
        P: IOPProverWithNoOracleRefs<F>,
        V: IOPVerifierWithGadget<S, F, PublicInput = P::PublicInput>,
        L: LDTWithGadget<F>,
    >(
        sponge: S,
        sponge_var: S::Var,
        public_input: &P::PublicInput,
        private_input: &P::PrivateInput,
        prover_parameter: &P::ProverParameter,
        verifier_parameter: &V::VerifierParameter,
        ldt_params: &L::LDTParameters,
        hash_params: MTHashParameters<MT>,
    ) where
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<F>,
    {
        // generate transcript using prover perspective
        let transcript_pt = {
            let mut transcript = Transcript::new(
                sponge.clone(),
                hash_params,
                |degree| L::ldt_info(ldt_params, degree),
                iop_trace!("check commit phase correctness"),
            );
            P::prove(
                NameSpace::root(iop_trace!("check commit phase correctness")),
                &(),
                public_input,
                private_input,
                &mut transcript,
                prover_parameter,
            )
            .unwrap();
            transcript
        };
        let cs = sponge_var.cs();
        let succinct_prover_messages = transcript_pt
            .all_succinct_round_oracles()
            .into_iter()
            .map(|round| SuccinctRoundOracleVar::new_witness(cs.clone(), || Ok(round)).unwrap())
            .collect::<Vec<_>>();
        let prover_mt_roots = transcript_pt
            .merkle_tree_roots()
            .into_iter()
            .map(|root| {
                root.map(|root| MTG::InnerDigest::new_witness(cs.clone(), || Ok(root)).unwrap())
            })
            .collect::<Vec<_>>();
        let sponge_var_vt = sponge_var.clone();
        let mut transcript_vt = SimulationTranscriptVar::<F, MT, MTG, S>::from_prover_messages(
            &succinct_prover_messages,
            &prover_mt_roots,
            sponge_var_vt,
            |degree| L::ldt_info(ldt_params, degree),
            iop_trace!("check commit phase correctness"),
        );
        V::register_iop_structure_var(
            NameSpace::root(iop_trace!("check commit phase correctness")),
            &mut transcript_vt,
            verifier_parameter,
        )
        .unwrap();
        check_transcript_var_consistency(&transcript_pt, &transcript_vt);
    }
}
