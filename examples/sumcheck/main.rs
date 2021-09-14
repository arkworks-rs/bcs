#[macro_use]
extern crate ark_bcs;

use ark_bls12_381::fr::Fr;
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_ldt::{domain::Radix2CosetDomain, fri::FRIParameters};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Radix2EvaluationDomain, UVPolynomial,
};
use ark_sponge::{poseidon::PoseidonSponge, Absorb, CryptographicSponge};
use ark_std::{marker::PhantomData, test_rng, One};

use ark_bcs::{
    bcs::{
        prover::BCSProof,
        transcript::{create_subprotocol_namespace, NameSpace, SimulationTranscript, Transcript},
        MTHashParameters,
    },
    iop::{
        message::{MessagesCollection, ProverRoundMessageInfo, RoundOracle, VerifierMessage},
        prover::IOPProver,
        verifier::IOPVerifier,
    },
    ldt::rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters},
    Error,
};

use crate::{
    simple_sumcheck::{
        SimpleSumcheck, SumcheckOracleRef, SumcheckProverParameter, SumcheckPublicInput,
    },
    test_utils::{poseidon_parameters, FieldMTConfig},
};

mod simple_sumcheck;
mod test_utils;

/// This protocol takes 3 polynomial coefficients as private input (as well as
/// its sum over summation domain). The protocol send those three oracles to
/// verifier, and run simple sumcheck on each of them.
pub struct SumcheckExample<F: PrimeField + Absorb> {
    _field: PhantomData<F>,
}

pub struct PublicInput<F: PrimeField + Absorb> {
    evaluation_domain: Radix2EvaluationDomain<F>,
    summation_domain: Radix2EvaluationDomain<F>,
    degrees: (usize, usize, usize),
    sums: (F, F, F),
}

pub struct PrivateInput<F: PrimeField + Absorb>(
    DensePolynomial<F>,
    DensePolynomial<F>,
    DensePolynomial<F>,
);

impl<F: PrimeField + Absorb> IOPProver<F> for SumcheckExample<F> {
    type ProverParameter = ();
    type RoundOracleRefs = ();
    type PublicInput = PublicInput<F>;
    type PrivateInput = PrivateInput<F>;

    fn prove<MT: Config<Leaf = [F]>, S: CryptographicSponge>(
        namespace: &NameSpace,
        _oracle_refs: &Self::RoundOracleRefs,
        public_input: &Self::PublicInput,
        private_input: &Self::PrivateInput,
        transcript: &mut Transcript<MT, S, F>,
        _prover_parameter: &Self::ProverParameter,
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb,
    {
        // first, send those 3 polynomial oracles in one round
        transcript.send_univariate_polynomial(public_input.degrees.0, &private_input.0)?;
        transcript.send_univariate_polynomial(public_input.degrees.1, &private_input.1)?;
        transcript.send_univariate_polynomial(public_input.degrees.2, &private_input.2)?;
        let round_ref = transcript.submit_prover_current_round(
            namespace,
            iop_trace!("polynomials for sumcheck example"),
        )?;

        // invoke sumcheck subprotocol
        let sumcheck_namespaces = (0..3)
            .map(|id| {
                let ns = create_subprotocol_namespace(namespace, id);
                transcript.new_namespace(ns.clone(), iop_trace!("sumcheck subprotocol"));
                ns
            })
            .collect::<Vec<_>>();

        // do sumcheck on each polynomial

        SimpleSumcheck::prove(
            &sumcheck_namespaces[0],
            &SumcheckOracleRef::new(round_ref),
            &SumcheckPublicInput::new(
                public_input.evaluation_domain,
                public_input.summation_domain,
                public_input.degrees.0,
                public_input.sums.0,
                0,
            ),
            &(),
            transcript,
            &SumcheckProverParameter {
                coeffs: private_input.0.clone(),
            },
        )?;

        SimpleSumcheck::prove(
            &sumcheck_namespaces[1],
            &SumcheckOracleRef::new(round_ref),
            &SumcheckPublicInput::new(
                public_input.evaluation_domain,
                public_input.summation_domain,
                public_input.degrees.1,
                public_input.sums.1,
                1,
            ),
            &(),
            transcript,
            &SumcheckProverParameter {
                coeffs: private_input.1.clone(),
            },
        )?;

        SimpleSumcheck::prove(
            &sumcheck_namespaces[2],
            &SumcheckOracleRef::new(round_ref),
            &SumcheckPublicInput::new(
                public_input.evaluation_domain,
                public_input.summation_domain,
                public_input.degrees.2,
                public_input.sums.2,
                2,
            ),
            &(),
            transcript,
            &SumcheckProverParameter {
                coeffs: private_input.2.clone(),
            },
        )?;

        Ok(())
    }
}

impl<S: CryptographicSponge, F: PrimeField + Absorb> IOPVerifier<S, F> for SumcheckExample<F> {
    type VerifierOutput = bool;
    type VerifierParameter = ();
    type OracleRefs = ();
    type PublicInput = PublicInput<F>;

    fn restore_from_commit_phase<MT: Config<Leaf = [F]>>(
        namespace: &NameSpace,
        public_input: &Self::PublicInput,
        transcript: &mut SimulationTranscript<MT, S, F>,
        _verifier_parameter: &Self::VerifierParameter,
    ) where
        MT::InnerDigest: Absorb,
    {
        transcript.receive_prover_current_round(
            namespace,
            ProverRoundMessageInfo::new(
                vec![
                    public_input.degrees.0,
                    public_input.degrees.1,
                    public_input.degrees.2,
                ],
                0,
                0,
                public_input.evaluation_domain.size(),
                0, // localization parameter managed by LDT
            ),
            iop_trace!("polynomials for sumcheck example"),
        );
        let sumcheck_namespaces = (0..3)
            .map(|id| {
                let ns = create_subprotocol_namespace(namespace, id);
                transcript.new_namespace(ns.clone(), iop_trace!("sumcheck subprotocol"));
                ns
            })
            .collect::<Vec<_>>();

        SimpleSumcheck::restore_from_commit_phase(
            &sumcheck_namespaces[0],
            &SumcheckPublicInput::new(
                public_input.evaluation_domain,
                public_input.summation_domain,
                public_input.degrees.0,
                public_input.sums.0,
                0,
            ),
            transcript,
            &(),
        );
        SimpleSumcheck::restore_from_commit_phase(
            &sumcheck_namespaces[1],
            &SumcheckPublicInput::new(
                public_input.evaluation_domain,
                public_input.summation_domain,
                public_input.degrees.1,
                public_input.sums.1,
                1,
            ),
            transcript,
            &(),
        );
        SimpleSumcheck::restore_from_commit_phase(
            &sumcheck_namespaces[2],
            &SumcheckPublicInput::new(
                public_input.evaluation_domain,
                public_input.summation_domain,
                public_input.degrees.2,
                public_input.sums.2,
                2,
            ),
            transcript,
            &(),
        );
    }

    fn query_and_decide<O: RoundOracle<F>>(
        namespace: &NameSpace,
        _verifier_parameter: &Self::VerifierParameter,
        public_input: &Self::PublicInput,
        _oracle_refs: &Self::OracleRefs,
        sponge: &mut S,
        messages_in_commit_phase: &mut MessagesCollection<&mut O, VerifierMessage<F>>,
    ) -> Result<Self::VerifierOutput, Error> {
        // we need to provide sumcheck verifier the references to current oracle being
        // sent
        let oracle_refs_sumcheck =
            SumcheckOracleRef::new(*messages_in_commit_phase.prover_message_as_ref(namespace, 0));
        // invoke sumcheck subprotocol
        let sumcheck_namespaces = (0..3)
            .map(|id| create_subprotocol_namespace(namespace, id))
            .collect::<Vec<_>>();

        let mut result = SimpleSumcheck::query_and_decide(
            &sumcheck_namespaces[0],
            &(),
            &SumcheckPublicInput::new(
                public_input.evaluation_domain,
                public_input.summation_domain,
                public_input.degrees.0,
                public_input.sums.0,
                0,
            ),
            &oracle_refs_sumcheck,
            sponge,
            messages_in_commit_phase,
        )?;
        result = result
            && SimpleSumcheck::query_and_decide(
                &sumcheck_namespaces[1],
                &(),
                &SumcheckPublicInput::new(
                    public_input.evaluation_domain,
                    public_input.summation_domain,
                    public_input.degrees.1,
                    public_input.sums.1,
                    1,
                ),
                &oracle_refs_sumcheck,
                sponge,
                messages_in_commit_phase,
            )?;
        result = result
            && SimpleSumcheck::query_and_decide(
                &sumcheck_namespaces[2],
                &(),
                &SumcheckPublicInput::new(
                    public_input.evaluation_domain,
                    public_input.summation_domain,
                    public_input.degrees.2,
                    public_input.sums.2,
                    2,
                ),
                &oracle_refs_sumcheck,
                sponge,
                messages_in_commit_phase,
            )?;

        Ok(result)
    }
}

/// A simple univariate sumcheck (currently without ldt, which is completely
/// insecure). We assume that size of summation domain < degree of testing poly
/// < size of evaluation domain
fn main() {
    let mut rng = test_rng();
    let degrees = (69, 72, 75);
    let poly0 = DensePolynomial::<Fr>::rand(degrees.0, &mut rng);
    let poly1 = DensePolynomial::<Fr>::rand(degrees.1, &mut rng);
    let poly2 = DensePolynomial::<Fr>::rand(degrees.2, &mut rng);
    let summation_domain = Radix2EvaluationDomain::new(64).unwrap();
    let evaluation_domain = Radix2EvaluationDomain::new(256).unwrap();
    let fri_parameters = FRIParameters::new(
        128,
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
    let claimed_sum3 = Radix2CosetDomain::new(summation_domain.clone(), Fr::one())
        .evaluate(&poly2)
        .into_iter()
        .sum::<Fr>();

    let sponge = PoseidonSponge::new(&poseidon_parameters());
    let mt_hash_parameters = MTHashParameters::<FieldMTConfig> {
        leaf_hash_param: poseidon_parameters(),
        inner_hash_param: poseidon_parameters(),
    };

    let vp = PublicInput {
        sums: (claimed_sum1, claimed_sum2, claimed_sum3),
        degrees: (degrees.0, degrees.1, degrees.2),
        summation_domain,
        evaluation_domain,
    };
    let wp = PrivateInput(poly0, poly1, poly2);

    let _proof = BCSProof::generate::<
        SumcheckExample<Fr>,
        SumcheckExample<Fr>,
        LinearCombinationLDT<Fr>,
        _,
    >(
        sponge,
        &vp,
        &wp,
        &(),
        &ldt_parameter,
        mt_hash_parameters.clone(),
    )
    .expect("fail to generate proof");

    // TODO: write examples to verify this proof
}
