#[cfg(feature = "r1cs")]
mod constraints;
/// Contains the mock IOP prover and verifier to solely test correctness of
/// transcript.
pub(crate) mod mock;

use crate::{
    bcs::{
        prover::BCSProof,
        simulation_transcript::SimulationTranscript,
        tests::mock::{MockTest1Verifier, MockTestProver},
        verifier::BCSVerifier,
        MTHashParameters,
    },
    iop::{bookkeeper::NameSpace, verifier::IOPVerifier},
    ldt::{
        rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters},
        LDT,
    },
    test_utils::poseidon_parameters,
};
use ark_crypto_primitives::{
    crh::poseidon,
    merkle_tree::{Config, IdentityDigestConverter},
};
use ark_ldt::{domain::Radix2CosetDomain, fri::FRIParameters};
use ark_sponge::{poseidon::PoseidonSponge, CryptographicSponge};
use ark_std::{vec, One};

pub(crate) type Fr = ark_bls12_381::Fr;
pub(crate) type H = poseidon::CRH<Fr>;
pub(crate) type TwoToOneH = poseidon::TwoToOneCRH<Fr>;

pub(crate) struct FieldMTConfig;
impl Config for FieldMTConfig {
    type Leaf = [Fr];
    type LeafDigest = Fr;
    type LeafInnerDigestConverter = IdentityDigestConverter<Fr>;
    type InnerDigest = Fr;
    type LeafHash = H;
    type TwoToOneHash = TwoToOneH;
}

#[test]
/// Test if restore_state_from_commit_phase message works. This test uses a
/// dummy protocol described as `MockTestProver`.
fn test_bcs() {
    let fri_parameters = FRIParameters::new(
        64,
        vec![2, 2, 1],
        Radix2CosetDomain::new_radix2_coset(128, Fr::one()),
    );
    let ldt_parameters = LinearCombinationLDTParameters {
        fri_parameters,
        num_queries: 7,
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

    // verify if simulation transcript reconstructs correctly
    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let mut simulation_transcript = SimulationTranscript::new_transcript(
        &bcs_proof,
        sponge,
        LinearCombinationLDT::codeword_domain(&ldt_parameters),
        LinearCombinationLDT::localization_param(&ldt_parameters),
        iop_trace!("test bcs"),
    );
    MockTest1Verifier::register_iop_structure(
        NameSpace::root(iop_trace!("BCS Test")),
        &mut simulation_transcript,
        &(),
    );
    // verify should return no error
    let sponge = PoseidonSponge::new(&poseidon_parameters());
    assert!(
        BCSVerifier::verify::<MockTest1Verifier<Fr>, LinearCombinationLDT<Fr>, _>(
            sponge,
            &bcs_proof,
            &(),
            &(),
            &ldt_parameters,
            mt_hash_param
        )
        .expect("verification failed"),
        "test verifier returns false"
    );
}
