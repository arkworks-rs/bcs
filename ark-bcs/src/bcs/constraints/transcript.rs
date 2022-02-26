use crate::{
    bcs::{constraints::proof::BCSProofVar, transcript::LDTInfo},
    iop::{
        bookkeeper::{MessageBookkeeper, NameSpace},
        constraints::{
            message::VerifierMessageVar,
            oracles::{VirtualOracleVar, VirtualOracleVarWithInfo},
        },
        message::{LeavesType, MsgRoundRef, ProverRoundMessageInfo},
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
use ark_std::{mem::take, vec::Vec, boxed::Box};

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
    pub(crate) expected_prover_messages_info: Vec<ProverRoundMessageInfo>,

    pub(crate) proof: &'a BCSProofVar<MT, MTG, F>,

    pub(crate) sponge: S::Var,
    pub(crate) current_prover_round: usize,
    pub(crate) reconstructed_verifier_messages: Vec<Vec<VerifierMessageVar<F>>>,

    pending_verifier_messages: Vec<VerifierMessageVar<F>>,
    pub(crate) bookkeeper: MessageBookkeeper,

    pub(crate) ldt_codeword_domain: Option<Radix2CosetDomain<F>>,
    pub(crate) ldt_localization_parameter: Option<usize>,

    /// Virtual oracle registered during commit phase simulation
    pub(crate) registered_virtual_oracles: Vec<VirtualOracleVarWithInfo<F>>,
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
        Self {
            proof: bcs_proof,
            expected_prover_messages_info: Vec::new(),
            ldt_codeword_domain,
            ldt_localization_parameter,
            sponge,
            current_prover_round: 0,
            reconstructed_verifier_messages: Vec::new(),
            pending_verifier_messages: Vec::new(),
            bookkeeper: MessageBookkeeper::new(trace),
            registered_virtual_oracles: Vec::new(),
        }
    }

    /// Create a new namespace in this transcript
    pub fn new_namespace(&mut self, current_namespace: NameSpace, trace: TraceInfo) -> NameSpace {
        self.bookkeeper.new_namespace(trace, current_namespace.id)
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
        expected_message_info: ProverRoundMessageInfo,
        trace: TraceInfo,
    ) -> Result<MsgRoundRef, SynthesisError> {
        if expected_message_info.reed_solomon_code_degree_bound.len() > 0 {
            // LDT is used. This prover round must not use custom domain.
            assert_eq!(expected_message_info.leaves_type, LeavesType::UseCodewordDomain,
                       "This round contains low-degree oracle, but custom length and localization parameter is used. ");
        }

        let index = self.current_prover_round;
        self.current_prover_round += 1;

        let trace_info = {
            ark_std::format!(
                "\n Message trace: {}\n Namespace trace: {}",
                trace,
                ns.trace
            )
        };

        if index >= self.proof.prover_iop_messages_by_round.len() {
            panic!(
                "Verifier tried to receive extra prove round message. {}",
                trace_info
            );
        }

        // check basic consistency with message received
        let current_round = &self.proof.prover_iop_messages_by_round[index];
        let num_short_message_expected = expected_message_info.num_short_messages;
        let num_short_message_received = current_round.short_messages.len();
        let num_oracles_expected = expected_message_info.num_oracles();
        let num_oracles_received = current_round.queried_cosets.get(0).map_or(0, |c| c.len());

        // here are some sanity check to make sure user is not doing wrong thing
        // check 1: `num_short_messages` and `num_oracles` should be consistent with
        // expected
        assert_eq!(
            num_short_message_expected, num_short_message_received,
            "Number of short messages received is not equal to expected. {}",
            trace_info
        );
        assert_eq!(
            num_oracles_expected, num_oracles_received,
            "Number of oracles received is not equal to expected. {}",
            trace_info
        );
        // check 2: number of oracles in each query result should be the same
        current_round.queried_cosets.iter().for_each(|c| {
            assert_eq!(
                c.len(),
                num_oracles_expected,
                "Number of oracles in each query result is not equal to expected. {}",
                trace_info
            );
        });
        // check 3: number of rs-codes should not exceed number of oracles
        assert!(
            expected_message_info.reed_solomon_code_degree_bound.len() <= num_oracles_expected,
            "Number of Reed-Solomon codes is greater than number of oracles. {}",
            trace_info
        );
        // check 4: if there are rs-codes, LeavesType should be UseCodewordDomain
        if expected_message_info.reed_solomon_code_degree_bound.len() > 0 {
            assert_eq!(
                expected_message_info.leaves_type,
                LeavesType::UseCodewordDomain,
                "If there are Reed-Solomon codes, leaves type should be UseCodewordDomain. {}",
                trace_info
            );
        }
        // check 5: if LeavesType is UseCodewordDomain, then length and localization
        // parameter should be same as length and localization for transcript
        if expected_message_info.leaves_type == LeavesType::UseCodewordDomain {
            assert_eq!(
                expected_message_info.length,
                self.ldt_codeword_domain.expect("codeword domain is not set").size(),
                "If leaves type is UseCodewordDomain, then length and localization parameter should be same as length and localization for transcript. {}",
                trace_info
            );
            assert_eq!(
                expected_message_info.localization_parameter,
                self.ldt_localization_parameter.expect("localization parameter is not set"),
                "If leaves type is UseCodewordDomain, then length and localization parameter should be same as length and localization for transcript. {}",
                trace_info
            );
        }

        // check 6.1: if there are no message oracles, length and localization parameter
        // should be 0
        if num_oracles_expected == 0 {
            assert_eq!(
                expected_message_info.length, 0,
                "If there are no message oracles, length should be 0. {}",
                trace_info
            );
            assert_eq!(
                expected_message_info.localization_parameter, 0,
                "If there are no message oracles, localization parameter should be 0. {}",
                trace_info
            );
        }
        // check 6.2: if there are message oracles length should be power of 2, and
        // 2^localization_parameter should <= length
        else {
            assert!(
                expected_message_info.length.is_power_of_two(),
                "Length should be power of 2. {}",
                trace_info
            );
            assert!(
                (1 << expected_message_info.localization_parameter) <= expected_message_info.length,
                "2^localization_parameter should <= oracle length. {}",
                trace_info
            );
        }

        // absorb merkle tree root, if any
        self.sponge
            .absorb(&self.proof.prover_messages_mt_root[index])?;
        // absorb short messages for this round, if any
        self.proof.prover_iop_messages_by_round[index]
            .short_messages
            .iter()
            .try_for_each(|msg| self.sponge.absorb(msg))?;
        // attach prover info to transcript
        self.expected_prover_messages_info
            .push(expected_message_info);
        Ok(self.attach_latest_prover_round_to_namespace(ns, false, trace))
    }

    /// register a virtual oracle constraints specified by coset evaluator
    pub fn register_prover_virtual_round<VO: VirtualOracleVar<F>>(
        &mut self,
        ns: NameSpace,
        oracle: VO,
        test_bound: Vec<usize>,
        constraint_bound: Vec<usize>,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        let (codeword_domain, localization_param) = (
            self.codeword_domain(),
            self.codeword_localization_parameter(),
        );
        assert!(!self.is_pending_message_available());
        let virtual_oracle = VirtualOracleVarWithInfo::new(
            Box::new(oracle),
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
        trace: TraceInfo,
    ) -> MsgRoundRef {
        let pending_message = take(&mut self.pending_verifier_messages);
        self.reconstructed_verifier_messages.push(pending_message);
        self.attach_latest_verifier_round_to_namespace(namespace, trace)
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
    fn codeword_domain(&self) -> Radix2CosetDomain<F> {
        self.ldt_codeword_domain.expect("LDT not enabled")
    }

    /// Return the localization parameter used by LDT. Localization parameter is
    /// the size of query coset of the codeword.
    ///
    /// ## Panics
    /// This function panics if LDT is not enabled or localization parameter is
    /// not supported by LDT.
    fn codeword_localization_parameter(&self) -> usize {
        self.ldt_localization_parameter
            .expect("LDT not enabled or localization parameter is not supported by LDT")
    }
}
