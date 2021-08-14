use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_sponge::Absorb;
use std::marker::PhantomData;
use crate::iop::constraints::IOPVerifierWithGadget;
use crate::ldt_trait::constraints::LDTWithGadget;
use ark_sponge::constraints::{SpongeWithGadget, AbsorbGadget};
use crate::bcs::constraints::proof::BCSProofVar;
use ark_r1cs_std::fields::fp::FpVar;
use crate::bcs::transcript::{SimulationTranscript, ROOT_NAMESPACE};
use crate::bcs::constraints::transcript::SimulationTranscriptVar;

pub struct BCSVerifierGadget<MT, MTG, CF>
where
    MT: Config,
    MTG: ConfigGadget<MT, CF>,
    CF: PrimeField + Absorb,
{
    _merkle_tree_config: PhantomData<(MT, MTG)>,
    _field: PhantomData<CF>,
}

impl<MT, MTG, CF> BCSVerifierGadget<MT, MTG, CF>
where
    MT: Config,
    MTG: ConfigGadget<MT, CF, Leaf=[FpVar<CF>]>,
    CF: PrimeField + Absorb,
    MT::InnerDigest: Absorb,
    MTG::InnerDigest: AbsorbGadget<CF>
{
    pub fn verify<V, L, S>(
        mut sponge: S::Var,
        proof: &BCSProofVar<MT, MTG, CF>,
        public_input: &V::PublicInputVar,
        verifier_parameter: &V::VerifierParameter,
        ldt_params: &L::LDTParameters
    ) -> Result<(), crate::Error>
    where V: IOPVerifierWithGadget<CF, S>,
    L: LDTWithGadget<CF>,
    S: SpongeWithGadget<CF>
    {
        // simulate main prove
        let (verifier_messages, bookkeeper, num_rounds_submitted) = {
            let mut transcript = SimulationTranscriptVar::new_transcript(proof, &mut sponge);
            V::restore_from_commit_phase_var(&ROOT_NAMESPACE, public_input, &mut transcript, verifier_parameter)?;
            assert!(
                !transcript.is_pending_message_available(),
                "Sanity check failed: pending verifier message not submitted"
            );
            assert_eq!(transcript.current_prover_round, proof.prover_iop_messages_by_round.len(),
             "Sanity check failed: transcript's all prover messages are not absorbed");
            let num_rounds_submitted = transcript.num_prover_rounds_submitted();
            (
            transcript.reconstructed_verifer_messages,
                transcript.bookkeeper,
                num_rounds_submitted
            )
        };

        // construct view of oracle
        let mut prover_messages_view: Vec<_> = proof.prover_iop_messages_by_round[..num_rounds_submitted]
            .iter().map(|msg|msg.get_view())
            .collect();
        let mut ldt_prover_messages_view: Vec<_> = proof.prover_iop_messages_by_round[num_rounds_submitted..]
            .iter().map(|msg|msg.get_view())
            .collect();





        todo!()
    }
}
