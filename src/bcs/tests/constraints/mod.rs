use ark_crypto_primitives::crh::poseidon;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::IdentityDigestConverter;
use ark_r1cs_std::fields::fp::FpVar;

use crate::bcs::constraints::proof::BCSProofVar;
use crate::bcs::constraints::transcript::SimulationTranscriptVar;
use crate::bcs::constraints::verifier::BCSVerifierGadget;
use crate::bcs::constraints::MTHashParametersVar;
use crate::bcs::tests::mock::MockTest1Verifier;
use crate::bcs::tests::{mock_test1_prove_with_transcript, FieldMTConfig, Fr};
use crate::bcs::transcript::ROOT_NAMESPACE;
use crate::iop::constraints::IOPVerifierWithGadget;
use crate::test_utils::poseidon_parameters;
use ark_crypto_primitives::crh::poseidon::constraints::CRHParametersVar;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::ConstraintSystem;
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_sponge::poseidon::PoseidonSponge;

mod mock;

type HG = poseidon::constraints::CRHGadget<Fr>;
type TwoToOneHG = poseidon::constraints::TwoToOneCRHGadget<Fr>;

impl ConfigGadget<Self, Fr> for FieldMTConfig {
    type Leaf = [FpVar<Fr>];
    type LeafDigest = FpVar<Fr>;
    type LeafInnerConverter = IdentityDigestConverter<FpVar<Fr>>;
    type InnerDigest = FpVar<Fr>;
    type LeafHash = HG;
    type TwoToOneHash = TwoToOneHG;
}

#[test]
fn test_bcs_var_no_ldt() {
    let (bcs_proof, expected_prove_transcript) = mock_test1_prove_with_transcript();
    let cs = ConstraintSystem::<Fr>::new_ref();
    let mt_hash_param = MTHashParametersVar::<Fr, FieldMTConfig, FieldMTConfig> {
        leaf_params: CRHParametersVar::new_constant(cs.clone(), poseidon_parameters()).unwrap(),
        inner_params: CRHParametersVar::new_constant(cs.clone(), poseidon_parameters()).unwrap(),
    };

    let bcs_proof_var =
        BCSProofVar::<_, FieldMTConfig, _>::new_witness(cs.clone(), || Ok(&bcs_proof)).unwrap();

    // verify if simulation transcript reconstructs correctly
    let mut sponge = PoseidonSpongeVar::new(cs.clone(), &poseidon_parameters());
    let mut simulation_transcript =
        SimulationTranscriptVar::<_, _, _, PoseidonSponge<_>>::new_transcript(
            &bcs_proof_var,
            &mut sponge,
            |_|panic!("ldt not used")
        );
    MockTest1Verifier::restore_from_commit_phase_var(
        &ROOT_NAMESPACE,
        &(),
        &mut simulation_transcript,
        &(),
    )
    .unwrap();
    simulation_transcript.check_correctness(&expected_prove_transcript);

    // verify should have all enforced constraints satisfied
    let sponge = PoseidonSpongeVar::new(cs.clone(), &poseidon_parameters());
    let result =
        BCSVerifierGadget::verify_with_ldt_disabled::<MockTest1Verifier<Fr>, PoseidonSponge<Fr>>(
            cs.clone(),
            sponge,
            &bcs_proof_var,
            &(),
            &(),
            &mt_hash_param,
        )
        .expect("error during verify");
    assert!(result.value().unwrap());

    assert!(cs.is_satisfied().unwrap());
}
