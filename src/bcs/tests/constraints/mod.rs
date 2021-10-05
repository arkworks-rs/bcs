use ark_crypto_primitives::{
    crh::poseidon,
    merkle_tree::{constraints::ConfigGadget, IdentityDigestConverter},
};
use ark_r1cs_std::fields::fp::FpVar;

use crate::{
    bcs::{
        constraints::{
            proof::BCSProofVar,
            transcript::{test_utils::check_commit_phase_correctness_var, SimulationTranscriptVar},
            verifier::BCSVerifierGadget,
            MTHashParametersVar,
        },
        prover::BCSProof,
        tests::{
            mock::{MockTest1Verifier, MockTestProver},
            FieldMTConfig, Fr,
        },
        transcript::NameSpace,
        MTHashParameters,
    },
    iop::constraints::IOPVerifierWithGadget,
    ldt::{
        rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters},
        LDT,
    },
    test_utils::poseidon_parameters,
};
use ark_crypto_primitives::crh::poseidon::constraints::CRHParametersVar;
use ark_ldt::{domain::Radix2CosetDomain, fri::FRIParameters};
use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
use ark_relations::r1cs::ConstraintSystem;
use ark_sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
    CryptographicSponge,
};
use ark_std::{vec, One};

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
/// Test register_iop_structure_var
fn test_register() {
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
    check_commit_phase_correctness_var::<
        Fr,
        _,
        FieldMTConfig,
        FieldMTConfig,
        MockTestProver<Fr>,
        MockTest1Verifier<Fr>,
        LinearCombinationLDT<Fr>,
    >(
        sponge,
        sponge_var,
        &(),
        &(),
        &(),
        &(),
        &ldt_parameters,
        mt_hash_param,
    );
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
            iop_trace!("bcs test"),
        );
    MockTest1Verifier::register_iop_structure_var(
        NameSpace::root(iop_trace!("BCS test")),
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
