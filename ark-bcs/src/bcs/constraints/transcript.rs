use crate::{
    bcs::{constraints::proof::BCSProofVar, transcript::LDTInfo},
    iop::{
        bookkeeper::{MessageBookkeeper, NameSpace},
        constraints::{
            message::VerifierMessageVar,
            oracles::{CosetVarEvaluator, SuccinctRoundMessageVar, VirtualOracleVar},
        },
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
use ark_std::{mem::take, vec::Vec};

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

    pub(crate) ldt_codeword_domain: Option<Radix2CosetDomain<F>>,
    pub(crate) ldt_localization_parameter: Option<usize>,

    /// Virtual oracle registered during commit phase simulation
    pub(crate) registered_virtual_oracles: Vec<VirtualOracleVar<F>>,
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
        ldt_codeword_domain: Option<Radix2CosetDomain<F>>,
        ldt_localization_parameter: Option<usize>,
        trace: TraceInfo,
    ) -> Self {
        let prover_short_messages: Vec<_> = bcs_proof
            .prover_iop_messages_by_round
            .iter()
            .map(|msg| &msg.short_messages)
            .collect();
        let prover_messages_info: Vec<_> = bcs_proof
            .prover_iop_messages_by_round
            .iter()
            .map(|msg| msg.info.clone())
            .collect();
        Self {
            prover_short_messages,
            prover_messages_info,
            prover_mt_roots: &bcs_proof.prover_messages_mt_root,
            sponge,
            current_prover_round: 0,
            bookkeeper: MessageBookkeeper::new(trace),
            reconstructed_verifier_messages: Vec::new(),
            pending_verifier_messages: Vec::new(),
            ldt_codeword_domain,
            ldt_localization_parameter,
            registered_virtual_oracles: Vec::new(),
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
        prover_iop_messages_by_round: &'a [SuccinctRoundMessageVar<F>],
        prover_iop_messages_mt_roots_by_round: &'a [Option<MTG::InnerDigest>],
        sponge_var: S::Var,
        ldt_codeword_domain: Option<Radix2CosetDomain<F>>,
        ldt_localization_parameter: Option<usize>,
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
            ldt_codeword_domain,
            ldt_localization_parameter,
            registered_virtual_oracles: Vec::new(),
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
    pub fn receive_prover_current_round(
        &mut self,
        ns: NameSpace,
        mut expected_message_info: ProverRoundMessageInfo,
        tracer: TraceInfo,
    ) -> Result<MsgRoundRef, SynthesisError> {
        if expected_message_info.reed_solomon_code_degree_bound.len() > 0 {
            expected_message_info.localization_parameter = self.ldt_localization_parameter();
        }

        let index = self.current_prover_round;
        self.current_prover_round += 1;

        let trace_info = {
            ark_std::format!(
                "\n Message trace: {}\n Namespace trace: {}",
                tracer,
                ns.trace
            )
        };

        if index >= self.prover_messages_info.len() {
            panic!(
                "Verifier tried to receive extra prove round message. {}",
                trace_info
            );
        }

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
        Ok(self.attach_latest_prover_round_to_namespace(ns, false, tracer))
    }

    /// register a virtual oracle constraints specified by coset evaluator
    pub fn register_prover_virtual_round(
        &mut self,
        ns: NameSpace,
        coset_evaluator: CosetVarEvaluator<F>,
        test_bound: Vec<usize>,
        constraint_bound: Vec<usize>,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        let (codeword_domain, localization_param) = (
            self.ldt_codeword_domain(),
            self.ldt_localization_parameter(),
        );
        let virtual_oracle = VirtualOracleVar::new(
            coset_evaluator,
            codeword_domain,
            localization_param,
            test_bound,
            constraint_bound,
        );

        self.registered_virtual_oracles.push(virtual_oracle);
        self.attach_latest_prover_round_to_namespace(ns, true, trace)
    }

    /// Submit all verification messages in this round
    pub fn submit_verifier_current_round(
        &mut self,
        namespace: NameSpace,
        tracer: TraceInfo,
    ) -> MsgRoundRef {
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
        is_virtual: bool,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        // add verifier message index to namespace
        let index = if is_virtual {
            self.registered_virtual_oracles.len() - 1
        } else {
            self.current_prover_round - 1
        };
        self.bookkeeper
            .attach_prover_round_to_namespace(namespace, index, is_virtual, trace)
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
}

impl<'a, F, MT, MTG, S> LDTInfo<F> for SimulationTranscriptVar<'a, F, MT, MTG, S>
where
    F: PrimeField + Absorb,
    MT: Config,
    MTG: ConfigGadget<MT, F, Leaf = [FpVar<F>]>,
    S: SpongeWithGadget<F>,
    MT::InnerDigest: Absorb,
    F: Absorb,
    MTG::InnerDigest: AbsorbGadget<F>,
{
    /// Return the codeword domain used by LDT.
    ///
    /// **Any low degree oracle will use this domain as evaluation domain.**
    ///
    /// ## Panics
    /// This function panics if LDT is not enabled.
    fn ldt_codeword_domain(&self) -> Radix2CosetDomain<F> {
        self.ldt_codeword_domain.expect("LDT not enabled")
    }

    /// Return the localization parameter used by LDT. Localization parameter is
    /// the size of query coset of the codeword.
    ///
    /// ## Panics
    /// This function panics if LDT is not enabled or localization parameter is
    /// not supported by LDT.
    fn ldt_localization_parameter(&self) -> usize {
        self.ldt_localization_parameter
            .expect("LDT not enabled or localization parameter is not supported by LDT")
    }
}
