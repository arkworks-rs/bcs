#![allow(unused)] // for this example only
use std::borrow::Borrow;

use ark_bls12_381::Fr;
use ark_crypto_primitives::{
    crh::poseidon,
    merkle_tree::{constraints::ConfigGadget, Config, IdentityDigestConverter},
};
use ark_ff::PrimeField;
use ark_ldt::{domain::Radix2CosetDomain, fri::FRIParameters};
use ark_poly::{EvaluationDomain, UVPolynomial};
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::fp::FpVar,
};
use ark_relations::r1cs::{
    ConstraintLayer, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, Namespace,
    SynthesisError, TracingMode,
};
use ark_sponge::{
    constraints::{AbsorbGadget, CryptographicSpongeVar, SpongeWithGadget},
    poseidon::{constraints::PoseidonSpongeVar, PoseidonParameters, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_std::{test_rng, One};

use ark_bcs::{
    bcs::{
        constraints::{
            proof::BCSProofVar, transcript::SimulationTranscriptVar, verifier::BCSVerifierGadget,
            MTHashParametersVar,
        },
        prover::BCSProof,
        transcript::NameSpace,
    },
    iop::{
        constraints::{
            message::{SuccinctRoundOracleVarView, VerifierMessageVar},
            IOPVerifierWithGadget,
        },
        message::{MessagesCollection, ProverRoundMessageInfo},
    },
    ldt::rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters},
};

use crate::{
    simple_sumcheck::{
        constraints::SumcheckPublicInputVar, SimpleSumcheck, SumcheckOracleRef,
        SumcheckVerifierParameter,
    },
    test_utils::poseidon_parameters,
    Parameter, PrivateInput, PublicInput, SumcheckExample,
};
use ark_bcs::bcs::MTHashParameters;
use tracing_subscriber::layer::SubscriberExt;

pub struct PublicInputVar<CF: PrimeField + Absorb> {
    sums: (FpVar<CF>, FpVar<CF>),
}

impl<CF: PrimeField + Absorb> AllocVar<PublicInput<CF>, CF> for PublicInputVar<CF> {
    fn new_variable<T: Borrow<PublicInput<CF>>>(
        cs: impl Into<Namespace<CF>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into().cs();
        let f = f()?;
        let val = f.borrow();
        Ok(Self {
            sums: (
                FpVar::new_variable(cs.clone(), || Ok(val.sums.0), mode)?,
                FpVar::new_variable(cs.clone(), || Ok(val.sums.1), mode)?,
            ),
        })
    }
}

impl<CF: PrimeField + Absorb, S: SpongeWithGadget<CF>> IOPVerifierWithGadget<S, CF>
    for SumcheckExample<CF>
{
    type VerifierOutputVar = Boolean<CF>;
    type PublicInputVar = PublicInputVar<CF>;

    fn register_iop_structure_var<MT: Config, MTG: ConfigGadget<MT, CF, Leaf = [FpVar<CF>]>>(
        namespace: NameSpace,
        transcript: &mut SimulationTranscriptVar<CF, MT, MTG, S>,
        verifier_parameter: &Self::VerifierParameter,
    ) -> Result<(), SynthesisError>
    where
        MT::InnerDigest: Absorb,
        MTG::InnerDigest: AbsorbGadget<CF>,
    {
        transcript.squeeze_verifier_field_elements(2)?;
        transcript
            .submit_verifier_current_round(namespace, iop_trace!("Verifier Random Coefficients"));

        transcript.receive_prover_current_round(
            namespace,
            ProverRoundMessageInfo::new(
                vec![verifier_parameter.degrees.0, verifier_parameter.degrees.1],
                0,
                0,
                verifier_parameter.evaluation_domain.size(),
                0,
            ),
            iop_trace!("two polynomials for sumcheck"),
        )?;

        let ns0 = transcript.new_namespace(namespace, iop_trace!("first sumcheck protocol"));
        SimpleSumcheck::register_iop_structure_var(
            ns0,
            transcript,
            &SumcheckVerifierParameter {
                degree: verifier_parameter.degrees.0,
                evaluation_domain: verifier_parameter.evaluation_domain,
                summation_domain: verifier_parameter.summation_domain,
            },
        )?;

        let ns1 = transcript.new_namespace(namespace, iop_trace!("second sumcheck protocol"));
        SimpleSumcheck::register_iop_structure_var(
            ns1,
            transcript,
            &SumcheckVerifierParameter {
                degree: verifier_parameter.degrees.1,
                evaluation_domain: verifier_parameter.evaluation_domain,
                summation_domain: verifier_parameter.summation_domain,
            },
        )?;
        Ok(())
    }

    fn query_and_decide_var(
        cs: ConstraintSystemRef<CF>,
        namespace: NameSpace,
        verifier_parameter: &Self::VerifierParameter,
        public_input: &Self::PublicInputVar,
        _oracle_refs: &Self::OracleRefs,
        sponge: &mut S::Var,
        messages_in_commit_phase: &mut MessagesCollection<
            &mut SuccinctRoundOracleVarView<CF>,
            VerifierMessageVar<CF>,
        >,
    ) -> Result<Self::VerifierOutputVar, SynthesisError> {
        // which oracle we are using to sumcheck
        let oracle_refs_sumcheck =
            SumcheckOracleRef::new(*messages_in_commit_phase.prover_message_as_ref(namespace, 0));
        let random_coeffs = messages_in_commit_phase.verifier_message(namespace, 0)[0]
            .clone()
            .try_into_field_elements()
            .expect("invalid verifier message type");

        let asserted_sums = (
            &public_input.sums.0 * &random_coeffs[0],
            &public_input.sums.1 * &random_coeffs[1],
        );

        // invoke first sumcheck protocol
        let result1 = <SimpleSumcheck<_> as IOPVerifierWithGadget<S, _>>::query_and_decide_var(
            ark_relations::ns!(cs, "first sumcheck").cs(),
            messages_in_commit_phase.get_subprotocol_namespace(namespace, 0),
            &SumcheckVerifierParameter {
                degree: verifier_parameter.degrees.0,
                evaluation_domain: verifier_parameter.evaluation_domain,
                summation_domain: verifier_parameter.summation_domain,
            },
            &SumcheckPublicInputVar::new(asserted_sums.0, 0),
            &oracle_refs_sumcheck,
            sponge,
            messages_in_commit_phase,
        )?;

        let result2 = <SimpleSumcheck<_> as IOPVerifierWithGadget<S, _>>::query_and_decide_var(
            ark_relations::ns!(cs, "first sumcheck").cs(),
            messages_in_commit_phase.get_subprotocol_namespace(namespace, 1),
            &SumcheckVerifierParameter {
                degree: verifier_parameter.degrees.1,
                evaluation_domain: verifier_parameter.evaluation_domain,
                summation_domain: verifier_parameter.summation_domain,
            },
            &SumcheckPublicInputVar::new(asserted_sums.1, 1),
            &oracle_refs_sumcheck,
            sponge,
            messages_in_commit_phase,
        )?;

        result1.and(&result2)
    }
}

struct SumcheckExampleVerification {
    // Constants embedded into the circuit: some parameters, for example
    param: Parameter<Fr>,
    poseidon_param: PoseidonParameters<Fr>, /* for simplicity, same poseidon parameter is used
                                             * for both merkle tree, and sponge */
    ldt_param: LinearCombinationLDTParameters<Fr>,

    // public input is the public input known by the verifier
    vp: PublicInput<Fr>,

    // private witness: we want to show we know the proof for the sumcheck example
    proof: BCSProof<FieldMTConfig, Fr>,
}

pub(crate) struct FieldMTConfig;
impl Config for FieldMTConfig {
    type Leaf = [Fr];
    type LeafDigest = Fr;
    type LeafInnerDigestConverter = IdentityDigestConverter<Fr>;
    type InnerDigest = Fr;
    type LeafHash = poseidon::CRH<Fr>;
    type TwoToOneHash = poseidon::TwoToOneCRH<Fr>;
}

pub(crate) struct FieldMTConfigGadget;
impl ConfigGadget<FieldMTConfig, Fr> for FieldMTConfigGadget {
    type Leaf = [FpVar<Fr>];
    type LeafDigest = FpVar<Fr>;
    type LeafInnerConverter = IdentityDigestConverter<FpVar<Fr>>;
    type InnerDigest = FpVar<Fr>;
    type LeafHash = poseidon::constraints::CRHGadget<Fr>;
    type TwoToOneHash = poseidon::constraints::TwoToOneCRHGadget<Fr>;
}

impl ConstraintSynthesizer<Fr> for SumcheckExampleVerification {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // allocate some constants for parameters
        let poseidon_param_var = poseidon::constraints::CRHParametersVar::new_constant(
            cs.clone(),
            &self.poseidon_param,
        )?;
        let mt_hash_param_var = MTHashParametersVar::<Fr, FieldMTConfig, FieldMTConfigGadget> {
            leaf_params: poseidon_param_var.clone(),
            inner_params: poseidon_param_var.clone(),
        };

        // first, allocate public inputs
        let vp_var = PublicInputVar::new_input(ark_relations::ns!(cs, "public input"), || {
            Ok(self.vp.clone())
        })?;

        // allocate proof
        let proof_var =
            BCSProofVar::new_witness(ark_relations::ns!(cs, "proof"), || Ok(self.proof.clone()))?;

        // write constraints to enforce the proof correctness
        let result = BCSVerifierGadget::verify::<
            SumcheckExample<Fr>,
            LinearCombinationLDT<Fr>,
            PoseidonSponge<Fr>,
        >(
            ark_relations::ns!(cs, "proof verification").cs(),
            PoseidonSpongeVar::new(cs.clone(), &self.poseidon_param),
            &proof_var,
            &vp_var,
            &self.param,
            &self.ldt_param,
            &mt_hash_param_var,
        )?;

        result.enforce_equal(&Boolean::TRUE)?;
        Ok(())
    }
}

#[test]
fn sumcheck_example_correctness() {
    use ark_poly::{univariate::DensePolynomial, Radix2EvaluationDomain};
    let mut rng = test_rng();
    let degrees = (155, 197);
    let poly0 = DensePolynomial::<Fr>::rand(degrees.0, &mut rng);
    let poly1 = DensePolynomial::<Fr>::rand(degrees.1, &mut rng);
    let summation_domain = Radix2EvaluationDomain::new(64).unwrap();
    let evaluation_domain = Radix2EvaluationDomain::new(512).unwrap();
    let fri_parameters = FRIParameters::new(
        256,
        vec![1, 3, 1],
        Radix2CosetDomain::new(evaluation_domain, Fr::one()),
    );
    let ldt_parameter = LinearCombinationLDTParameters {
        fri_parameters,
        num_queries: 3,
    };
    let claimed_sum1 = Radix2CosetDomain::new(summation_domain.clone(), Fr::one())
        .evaluate(&poly0)
        .into_iter()
        .sum::<Fr>();
    let claimed_sum2 = Radix2CosetDomain::new(summation_domain.clone(), Fr::one())
        .evaluate(&poly1)
        .into_iter()
        .sum::<Fr>();

    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let mt_hash_parameters = MTHashParameters::<FieldMTConfig> {
        leaf_hash_param: poseidon_parameters(),
        inner_hash_param: poseidon_parameters(),
    };

    let vp = PublicInput {
        sums: (claimed_sum1, claimed_sum2),
    };
    let wp = PrivateInput(poly0, poly1);
    let prover_param = Parameter {
        degrees,
        summation_domain,
        evaluation_domain,
    };

    let proof = BCSProof::generate::<
        SumcheckExample<Fr>,
        SumcheckExample<Fr>,
        LinearCombinationLDT<Fr>,
        _,
    >(
        sponge,
        &vp,
        &wp,
        &prover_param,
        &ldt_parameter,
        mt_hash_parameters.clone(),
    )
    .expect("fail to generate proof");

    let circuit = SumcheckExampleVerification {
        param: prover_param,
        poseidon_param: poseidon_parameters(),
        ldt_param: ldt_parameter.clone(),
        vp,
        proof,
    };

    // some debugging tools for constraints
    let mut layer = ConstraintLayer::default();
    layer.mode = TracingMode::OnlyConstraints;
    let subscriber = tracing_subscriber::Registry::default().with(layer);
    let _guard = tracing::subscriber::set_default(subscriber);
    // Next, let's make the circuit!
    let cs = ConstraintSystem::new_ref();
    circuit.generate_constraints(cs.clone()).unwrap();
    // Let's check whether the constraint system is satisfied
    let is_satisfied = cs.is_satisfied().unwrap();
    if !is_satisfied {
        // If it isn't, find out the offending constraint.
        println!("{:?}", cs.which_is_unsatisfied());
    }
    assert!(is_satisfied);

    // show number of constraints
    println!("number of constraints: {}", cs.num_constraints());
}
