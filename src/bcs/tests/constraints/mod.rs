use ark_crypto_primitives::crh::poseidon;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::IdentityDigestConverter;
use ark_r1cs_std::fields::fp::FpVar;

use crate::bcs::constraints::proof::BCSProofVar;
use crate::bcs::constraints::transcript::SimulationTranscriptVar;
use crate::bcs::constraints::verifier::BCSVerifierGadget;
use crate::bcs::constraints::MTHashParametersVar;
use crate::bcs::prover::BCSProof;
use crate::bcs::tests::mock::{MockTest1Verifier, MockTestProver};
use crate::bcs::tests::{FieldMTConfig, Fr};
use crate::bcs::transcript::ROOT_NAMESPACE;
use crate::bcs::MTHashParameters;
use crate::iop::constraints::IOPVerifierWithGadget;
use crate::ldt::rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters};
use crate::ldt::LDT;
use crate::test_utils::poseidon_parameters;
use ark_crypto_primitives::crh::poseidon::constraints::CRHParametersVar;
use ark_ldt::domain::Radix2CosetDomain;
use ark_ldt::fri::FRIParameters;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::ConstraintSystem;
use ark_sponge::constraints::CryptographicSpongeVar;
use ark_sponge::poseidon::constraints::PoseidonSpongeVar;
use ark_sponge::poseidon::PoseidonSponge;
use ark_sponge::CryptographicSponge;
use ark_std::One;
use crate::bcs::constraints::transcript::test_utils::check_commit_phase_correctness_var;

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
/// Test restore_from_commit_phase_var
fn test_restore() {
    let fri_parameters = FRIParameters::new(
        64,
        vec![1, 2, 1],
        Radix2CosetDomain::new_radix2_coset(128, Fr::one()),
    );
    let ldt_parameters = LinearCombinationLDTParameters {
        fri_parameters,
        num_queries: 1,
    };
    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let cs = ConstraintSystem::new_ref();
    let sponge_var = PoseidonSpongeVar::new(cs.clone(), &poseidon_parameters());
    let mt_hash_param = MTHashParameters::<FieldMTConfig> {
        leaf_hash_param: poseidon_parameters(),
        inner_hash_param: poseidon_parameters(),
    };
    check_commit_phase_correctness_var::<Fr, _, FieldMTConfig, FieldMTConfig, MockTestProver<Fr>, MockTest1Verifier<Fr>, LinearCombinationLDT<Fr>>
        (sponge, sponge_var, &(), &(), &(), &(), &(), &ldt_parameters, mt_hash_param);

}

#[test]
fn test_bcs() {

    let fri_parameters = FRIParameters::new(
        64,
        vec![1, 2, 1],
        Radix2CosetDomain::new_radix2_coset(128, Fr::one()),
    );
    let ldt_parameters = LinearCombinationLDTParameters {
        fri_parameters,
        num_queries: 1,
    };
    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let mt_hash_param = MTHashParameters::<FieldMTConfig> {
        leaf_hash_param: poseidon_parameters(),
        inner_hash_param: poseidon_parameters(),
    };
    let bcs_proof = BCSProof::generate::<
        MockTest1Verifier<Fr>,
        MockTestProver<Fr>,
        LinearCombinationLDT<Fr>,
        _,
    >(
        sponge,
        &(),
        &(),
        &(),
        &(),
        &ldt_parameters,
        mt_hash_param.clone(),
    )
    .expect("fail to prove");
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
            |degree| LinearCombinationLDT::ldt_info(&ldt_parameters, degree),
        );
    MockTest1Verifier::restore_from_commit_phase_var(
        &ROOT_NAMESPACE,
        &(),
        &mut simulation_transcript,
        &(),
    )
    .unwrap();

    // verify should have all enforced constraints satisfied
    let sponge = PoseidonSpongeVar::new(cs.clone(), &poseidon_parameters());
    let result = BCSVerifierGadget::verify::<
        MockTest1Verifier<Fr>,
        LinearCombinationLDT<Fr>,
        PoseidonSponge<Fr>,
    >(
        cs.clone(),
        sponge,
        &bcs_proof_var,
        &(),
        &(),
        &ldt_parameters,
        &mt_hash_param,
    )
    .expect("error during verify");
    assert!(result.value().unwrap());

    assert!(cs.is_satisfied().unwrap());
}
