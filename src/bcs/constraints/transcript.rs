use crate::bcs::constraints::message::VerifierMessageVar;
use crate::bcs::constraints::proof::BCSProofVar;
use crate::bcs::message::ProverRoundMessageInfo;
use crate::bcs::transcript::{MessageBookkeeper, NameSpace};
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::SynthesisError;
use ark_sponge::constraints::{AbsorbGadget, CryptographicSpongeVar, SpongeWithGadget};
use ark_sponge::Absorb;
use ark_std::mem::take;

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
    prover_messages_info: Vec<ProverRoundMessageInfo>,
    prover_mt_roots: &'a [Option<MTG::InnerDigest>],
    prover_short_messages: Vec<&'a Vec<Vec<FpVar<F>>>>,
    sponge: &'a mut S::Var,
    pub(crate) current_prover_round: usize,
    pub(crate) reconstructed_verifer_messages: Vec<Vec<VerifierMessageVar<F>>>,

    pending_verifier_messages: Vec<VerifierMessageVar<F>>,
    pub(crate) bookkeeper: MessageBookkeeper,
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
        sponge: &'a mut S::Var,
    ) -> Self {
        Self::new_transcript_with_offset(bcs_proof, 0, sponge)
    }

    pub(crate) fn new_transcript_with_offset(
        bcs_proof: &'a BCSProofVar<MT, MTG, F>,
        round_offset: usize,
        sponge: &'a mut S::Var,
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
            bookkeeper: MessageBookkeeper::default(),
            reconstructed_verifer_messages: Vec::new(),
            pending_verifier_messages: Vec::new(),
        }
    }

    pub(crate) fn num_prover_rounds_submitted(&self) -> usize {
        self.current_prover_round
    }

    pub fn receive_prover_current_round(
        &mut self,
        ns: &NameSpace,
        expected_message_info: &ProverRoundMessageInfo,
    ) -> Result<(), SynthesisError> {
        let index = self.current_prover_round;
        self.current_prover_round += 1;

        assert_eq!(
            expected_message_info, &self.prover_messages_info[index],
            "prover message is not what verifier want at current round"
        );

        // absorb merkle tree root, if any
        self.sponge.absorb(&self.prover_mt_roots[index])?;

        // absorb short messages for this round, if any
        self.prover_short_messages[index]
            .iter()
            .try_for_each(|msg| self.sponge.absorb(msg))?;
        self.attach_latest_prover_round_to_namespace(ns);

        Ok(())
    }

    /// Submit all verification messages in this round
    pub fn submit_verifier_current_round(&mut self, namespace: &NameSpace) {
        let pending_message = take(&mut self.pending_verifier_messages);
        self.reconstructed_verifer_messages.push(pending_message);
        self.attach_latest_verifier_round_to_namespace(namespace);
    }

    /// Squeeze sampled verifier message as field elements. The squeezed elements is attached to
    /// pending messages, and need to be submitted through `submit_verifier_current_round`.
    /// Submitted messages will be stored in transcript and will be later
    /// given to verifier in query and decision phase.
    ///
    /// **Note**: Since we are not running the actual prover code, verifier message is not used
    /// `reconstructed_verifer_messages`, so this function returns nothing.
    /// TODO: current limitation: sponge constraints does not support squeeze native elements with size
    pub fn squeeze_verifier_field_elements(
        &mut self,
        num_elements: usize,
    ) -> Result<(), SynthesisError> {
        let msg = self.sponge.squeeze_field_elements(num_elements)?;
        self.pending_verifier_messages
            .push(VerifierMessageVar::FieldElements(msg));
        Ok(())
    }

    /// Squeeze sampled verifier message as bytes. The squeezed bytes is attached to
    /// pending messages, and need to be submitted through `submit_verifier_current_round`.
    /// Submitted messages will be stored in transcript and will be later
    /// given to verifier in query and decision phase.
    ///
    /// **Note**: Since we are not running the actual prover code, verifier message is not used
    /// `reconstructed_verifer_messages`, so this function returns nothing.
    pub fn squeeze_verifier_field_bytes(&mut self, num_bytes: usize) -> Result<(), SynthesisError> {
        let msg = self.sponge.squeeze_bytes(num_bytes)?;
        self.pending_verifier_messages
            .push(VerifierMessageVar::Bytes(msg));
        Ok(())
    }

    /// Squeeze sampled verifier message as bytes. The squeezed bytes is attached to
    /// pending messages, and need to be submitted through `submit_verifier_current_round`.
    /// Submitted messages will be stored in transcript and will be later
    /// given to verifier in query and decision phase.
    ///
    /// **Note**: Since we are not running the actual prover code, verifier message is not used
    /// `reconstructed_verifer_messages`, so this function returns nothing.
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

    fn attach_latest_prover_round_to_namespace(&mut self, namespace: &NameSpace) {
        // add verifier message index to namespace
        let index = self.current_prover_round - 1;
        self.bookkeeper
            .fetch_node_mut(namespace)
            .expect("namespace not found")
            .prover_message_locations
            .push(index);
    }

    fn attach_latest_verifier_round_to_namespace(&mut self, namespace: &NameSpace) {
        // add verifier message index to namespace
        let index = self.reconstructed_verifer_messages.len() - 1;
        self.bookkeeper
            .fetch_node_mut(namespace)
            .expect("namespace not found")
            .verifier_message_locations
            .push(index);
    }
}

#[cfg(test)]
pub(crate) mod sanity_check {
    use crate::bcs::constraints::message::VerifierMessageVar;
    use crate::bcs::constraints::transcript::SimulationTranscriptVar;
    use crate::bcs::message::VerifierMessage;
    use crate::bcs::transcript::Transcript;
    use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
    use ark_crypto_primitives::merkle_tree::Config;
    use ark_ff::PrimeField;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::R1CSVar;
    use ark_sponge::constraints::{AbsorbGadget, SpongeWithGadget};
    use ark_sponge::Absorb;

    impl<'a, F, P, PG, S> SimulationTranscriptVar<'a, F, P, PG, S>
    where
        F: PrimeField + Absorb,
        P: Config<Leaf = [F]>,
        PG: ConfigGadget<P, F, Leaf = [FpVar<F>]>,
        S: SpongeWithGadget<F>,
        P::InnerDigest: Absorb,
        F: Absorb,
        PG::InnerDigest: AbsorbGadget<F>,
    {
        /// test whether `reconstructed_verifer_messages` simulate the prover-verifier interaction in
        /// commit phase correctly.
        pub fn check_correctness(&self, prover_transcript: &Transcript<P, S, F>) {
            // TODO: give information about which namespace is incorrect
            assert_eq!(prover_transcript.bookkeeper,
                       self.bookkeeper,
                       "your simulation code submits incorrect number of rounds, or call subprotocols in incorrect order.");

            // TODO: give information about which message in which namespace is incorrect
            prover_transcript
                .verifier_messages
                .iter()
                .zip(self.reconstructed_verifer_messages.iter())
                .for_each(|(expected, actual)| {
                    expected
                        .iter()
                        .zip(actual.iter())
                        .for_each(|(expected, actual)| match (expected, actual) {
                            (
                                VerifierMessage::FieldElements(expected),
                                VerifierMessageVar::FieldElements(actual),
                            ) => {
                                expected
                                    .iter()
                                    .zip(actual.iter())
                                    .for_each(|(expected, actual)| {
                                        assert_eq!(
                                            expected,
                                            &actual.value().expect("value not assigned!")
                                        )
                                    })
                            }
                            (
                                VerifierMessage::Bytes(expected),
                                VerifierMessageVar::Bytes(actual),
                            ) => {
                                assert_eq!(
                                    expected.as_slice(),
                                    actual.value().expect("value not assigned").as_slice()
                                )
                            }
                            (VerifierMessage::Bits(expected), VerifierMessageVar::Bits(actual)) => {
                                assert_eq!(
                                    expected.as_slice(),
                                    actual.value().expect("value not assigned").as_slice()
                                )
                            }
                            _ => panic!("verification message type mismatch!"),
                        })
                })
        }
    }
}
