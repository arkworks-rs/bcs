#[cfg(feature = "r1cs")]
mod constraints;
/// Contains the mock IOP prover and verifier to solely test correctness of transcript.
pub(crate) mod mock;

use crate::bcs::prover::BCSProof;
use crate::bcs::tests::mock::{MockTest1Prover, MockTest1Verifier};
use crate::bcs::transcript::{SimulationTranscript, Transcript, ROOT_NAMESPACE};
use crate::bcs::verifier::BCSVerifier;
use crate::bcs::MTHashParameters;
use crate::iop::prover::IOPProver;
use crate::iop::verifier::IOPVerifier;
use crate::ldt::{NoLDT, LDT};
use crate::test_utils::poseidon_parameters;
use ark_crypto_primitives::crh::poseidon;
use ark_crypto_primitives::merkle_tree::{Config, IdentityDigestConverter};
use ark_sponge::poseidon::PoseidonSponge;
use ark_sponge::CryptographicSponge;

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

pub(crate) fn mock_test1_prove_with_transcript() -> (
    BCSProof<FieldMTConfig, Fr>,
    Transcript<'static, FieldMTConfig, PoseidonSponge<Fr>, Fr>,
) {
    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let mt_hash_param = MTHashParameters::<FieldMTConfig> {
        leaf_hash_param: poseidon_parameters(),
        inner_hash_param: poseidon_parameters(),
    };
    // create a BCS transcript
    let mut expected_prove_transcript = Transcript::new(sponge, mt_hash_param.clone(), |degree| {
        NoLDT::ldt_info(&None, degree)
    });

    // run prover code, using transcript to sample verifier message
    // This is not a subprotocol, so we use root namespace (/).
    MockTest1Prover::prove(
        &ROOT_NAMESPACE,
        &mut (),
        &mut expected_prove_transcript,
        &(),
    )
    .unwrap();

    // generate bcs proof
    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let bcs_proof = BCSProof::generate_with_ldt_disabled::<
        MockTest1Verifier<Fr>,
        MockTest1Prover<Fr>,
        _,
    >(sponge, &(), &(), &(), &(), mt_hash_param.clone())
    .expect("fail to prove");

    (bcs_proof, expected_prove_transcript)
}

#[test]
/// Test if restore_state_from_commit_phase message works
fn test_bcs_no_ldt() {
    let (bcs_proof, expected_prove_transcript) = mock_test1_prove_with_transcript();

    let mt_hash_param = MTHashParameters::<FieldMTConfig> {
        leaf_hash_param: poseidon_parameters(),
        inner_hash_param: poseidon_parameters(),
    };

    // verify if simulation transcript reconstructs correctly
    let mut sponge = PoseidonSponge::new(&poseidon_parameters());
    let mut simulation_transcript =
        SimulationTranscript::new_transcript(&bcs_proof, &mut sponge, |_| panic!("ldt not used"));
    MockTest1Verifier::restore_from_commit_phase(
        &ROOT_NAMESPACE,
        &(),
        &mut simulation_transcript,
        &(),
    );
    simulation_transcript.check_correctness(&expected_prove_transcript);

    // verify should return no error
    let sponge = PoseidonSponge::new(&poseidon_parameters());
    assert!(
        BCSVerifier::verify_with_ldt_disabled::<MockTest1Verifier<Fr>, _>(
            sponge,
            &bcs_proof,
            &(),
            &(),
            mt_hash_param
        )
        .expect("verification failed"),
        "test verifier returns false"
    );
}
