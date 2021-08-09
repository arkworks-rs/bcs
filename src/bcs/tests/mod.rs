/// Contains the mock IOP prover and verifier to solely test correctness of transcript.
pub(crate) mod mock;

use ark_sponge::poseidon::PoseidonSponge;
use ark_sponge::CryptographicSponge;
use crate::test_utils::poseidon_parameters;
use crate::bcs::prover::BCSProof;
use crate::bcs::MTHashParameters;
use ark_crypto_primitives::merkle_tree::{Config, IdentityDigestConverter};
use ark_crypto_primitives::crh::poseidon;
use crate::bcs::tests::mock::{MockTest1Verifier, MockTest1Prover};
use crate::bcs::transcript::{Transcript, ROOT_NAMESPACE, SimulationTranscript};
use crate::iop::prover::IOPProver;
use crate::iop::verifier::IOPVerifier;

type Fr = ark_ed_on_bls12_381::Fr;
type H = poseidon::CRH<Fr>;
type TwoToOneH = poseidon::TwoToOneCRH<Fr>;

struct FieldMTConfig;
impl Config for FieldMTConfig {
    type Leaf = [Fr];
    type LeafDigest = Fr;
    type LeafInnerDigestConverter = IdentityDigestConverter<Fr>;
    type InnerDigest = Fr;
    type LeafHash = H;
    type TwoToOneHash = TwoToOneH;
}

#[test]
/// Test if restore_state_from_commit_phase message works
fn test_reconstruct() {
    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let mt_hash_param = MTHashParameters::<FieldMTConfig>{
        leaf_hash_param: poseidon_parameters(),
        inner_hash_param: poseidon_parameters()
    };
    // create a BCS transcript
    let mut expected_prove_transcript = Transcript::new(sponge, mt_hash_param.clone());

    // run prover code, using transcript to sample verifier message
    // This is not a subprotocol, so we use root namespace (/).
    MockTest1Prover::prove(
        &ROOT_NAMESPACE,
        &mut (),
        &mut expected_prove_transcript,
        &(),
    );

    // generate bcs proof
    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let bcs_proof = BCSProof::generate_without_ldt::<MockTest1Verifier<Fr>, MockTest1Prover<Fr>, _>(sponge,
                                                   &(),
                                                   &(),
                                                   &(),
                                                   &(),
                                                   mt_hash_param).expect("fail to prove");

    // verify simulation transcript
    let mut sponge = PoseidonSponge::new(&poseidon_parameters());
    let mut simulation_transcript = SimulationTranscript::new_main_transcript(&bcs_proof, &mut sponge);
    MockTest1Verifier::restore_state_from_commit_phase(&ROOT_NAMESPACE, &(), &mut simulation_transcript, &());
    simulation_transcript.check_correctness(&expected_prove_transcript);



}