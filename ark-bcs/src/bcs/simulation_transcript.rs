use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};
use ark_std::vec::Vec;
use tracing::info;

use crate::bcs::transcript::LDTInfo;
use crate::iop::message::LeavesType;
use crate::iop::oracles::VirtualOracle;
use crate::{
    bcs::prover::BCSProof,
    iop::{
        bookkeeper::{MessageBookkeeper, NameSpace},
        message::{MsgRoundRef, ProverRoundMessageInfo, VerifierMessage},
        oracles::VirtualOracleWithInfo,
    },
    tracer::TraceInfo,
};
use ark_ldt::domain::Radix2CosetDomain;
use ark_std::mem::take;

/// A wrapper for BCS proof, so that verifier can reconstruct verifier messages
/// by simulating commit phase easily.
/// TODO: add virtual oracle here
pub struct SimulationTranscript<
    'a,
    P: MTConfig<Leaf = [F]>,
    S: CryptographicSponge,
    F: PrimeField + Absorb,
> where
    P::InnerDigest: Absorb,
{
    /// prover round message info expected by verifier
    pub(crate) expected_prover_messages_info: Vec<ProverRoundMessageInfo>,

    // /// For each round submit, absorb merkle tree root first
    // prover_mt_roots: &'a [Option<P::InnerDigest>],
    // /// After absorb merkle tree root for this round, absorb the short messages
    // /// in entirety
    // prover_short_messages: Vec<&'a Vec<Vec<F>>>,
    pub(crate) proof: &'a BCSProof<P, F>,

    /// sponge is used to sample verifier message
    pub(crate) sponge: S,
    /// the next prover round message to absorb
    pub(crate) current_prover_round: usize,

    /// Those reconstructed messages will be used in query and decision phase
    pub(crate) reconstructed_verifier_messages: Vec<Vec<VerifierMessage<F>>>,

    pending_verifier_messages: Vec<VerifierMessage<F>>,
    pub(crate) bookkeeper: MessageBookkeeper,

    pub(crate) ldt_codeword_domain: Option<Radix2CosetDomain<F>>,
    pub(crate) ldt_localization_parameter: Option<usize>,

    /// Virtual oracle registered during commit phase simulation.
    pub(crate) registered_virtual_oracles: Vec<VirtualOracleWithInfo<F>>,
}


impl<'a, P: MTConfig<Leaf = [F]>, S: CryptographicSponge, F: PrimeField + Absorb>
    SimulationTranscript<'a, P, S, F>
where
    P::InnerDigest: Absorb,
{
    /// Returns a wrapper for BCS proof so that verifier can reconstruct
    /// verifier messages by simulating commit phase easily.
    pub(crate) fn new_transcript(
        bcs_proof: &'a BCSProof<P, F>,
        sponge: S,
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

    /// Create a new namespace in bookkeeper.
    pub fn new_namespace(&mut self, current_namespace: NameSpace, trace: TraceInfo) -> NameSpace {
        self.bookkeeper.new_namespace(trace, current_namespace.id)
    }

    /// Returns the number of prover rounds that prover have submitted.
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
    ) -> MsgRoundRef {
        info!("prover round: {}", trace);
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
        // check 1: `num_short_messages` and `num_oracles` should be consistent with expected
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
        // check 5: if LeavesType is UseCodewordDomain, then length and localization parameter should be same as length and localization for transcript
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

        // check 6.1: if there are no message oracles, length and localization parameter should be 0
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
        // check 6.2: if there are message oracles length should be power of 2, and 2^localization_parameter should <= length
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
            .absorb(&self.proof.prover_messages_mt_root[index]);
        // absorb short messages for this round, if any
        self.proof.prover_iop_messages_by_round[index]
            .short_messages
            .iter()
            .for_each(|msg| self.sponge.absorb(msg));
        // attach prover info to transcript
        self.expected_prover_messages_info
            .push(expected_message_info);
        self.attach_latest_prover_round_to_namespace(ns, false, trace)
    }

    /// Register a virtual oracle specified by coset evaluator.
    pub fn register_prover_virtual_round<VO: VirtualOracle<F>>(
        &mut self,
        ns: NameSpace,
        oracle: VO,
        test_bound: Vec<usize>,
        constraint_bound: Vec<usize>,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        info!("Register prover virtual oracle: {}", trace);
        // make sure that no virtual oracle is registered when we are halfway sampling
        // verifier round
        assert!(!self.is_pending_message_available());
        let (codeword_domain, localization_param) =
            (self.codeword_domain(), self.codeword_localization_parameter());
        let virtual_oracle = VirtualOracleWithInfo::new(
            Box::new(oracle),
            codeword_domain,
            localization_param,
            test_bound,
            constraint_bound,
        );

        self.registered_virtual_oracles.push(virtual_oracle);
        self.attach_latest_prover_round_to_namespace(ns, true, trace)
    }

    /// Submit all verifier messages in this round.
    pub fn submit_verifier_current_round(
        &mut self,
        namespace: NameSpace,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        info!("verifier round (sim): {}", trace);
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
    /// **Note**: In original IOP paper, verifier do not use sampled element in
    /// commit phase. So in this implementation, this function returns nothing.
    pub fn squeeze_verifier_field_elements(&mut self, field_size: &[FieldElementSize]) {
        let msg = self.sponge.squeeze_field_elements_with_sizes(field_size);
        self.pending_verifier_messages
            .push(VerifierMessage::FieldElements(msg));
    }

    /// Squeeze sampled verifier message as bytes. The squeezed bytes is
    /// attached to pending messages, and need to be submitted through
    /// `submit_verifier_current_round`. Submitted messages will be stored
    /// in transcript and will be later given to verifier in query and
    /// decision phase.
    ///
    /// **Note**: In original IOP paper, verifier do not use sampled element in
    /// commit phase. However, this implementation allows verifier to have
    /// access to sampled elements in `register_iop_structure` to
    /// add flexibility.
    /// User may need to check if this flexibility will affect soundness
    /// analysis in a case-to-case basis.
    pub fn squeeze_verifier_field_bytes(&mut self, num_bytes: usize) -> Vec<u8> {
        let msg = self.sponge.squeeze_bytes(num_bytes);
        self.pending_verifier_messages
            .push(VerifierMessage::Bytes(msg.clone()));
        msg
    }

    /// Squeeze sampled verifier message as bytes. The squeezed bytes is
    /// attached to pending messages, and need to be submitted through
    /// `submit_verifier_current_round`. Submitted messages will be stored
    /// in transcript and will be later given to verifier in query and
    /// decision phase.
    ///
    /// **Note**: In original IOP paper, verifier do not use sampled element in
    /// commit phase. However, this implementation allows verifier to have
    /// access to sampled elements in `register_iop_structure` to
    /// add flexibility.
    /// User may need to check if this flexibility will affect soundness
    /// analysis in a case-to-case basis.
    pub fn squeeze_verifier_field_bits(&mut self, num_bits: usize) -> Vec<bool> {
        let msg = self.sponge.squeeze_bits(num_bits);
        self.pending_verifier_messages
            .push(VerifierMessage::Bits(msg.clone()));
        msg
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

impl<
    'a,
    P: MTConfig<Leaf=[F]>,
    S: CryptographicSponge,
    F: PrimeField + Absorb,
> LDTInfo<F> for SimulationTranscript<'a, P, S, F> where
    P::InnerDigest: Absorb, {
    fn codeword_domain(&self) -> Radix2CosetDomain<F> {
        self.ldt_codeword_domain.expect("LDT not enabled")
    }

    fn codeword_localization_parameter(&self) -> usize {
        self.ldt_localization_parameter.expect("LDT not enabled")
    }
}