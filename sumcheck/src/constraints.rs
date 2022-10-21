use crate::UnivariateSumcheck;
use alloc::{vec, vec::Vec};
use ark_bcs::{
    bcs::constraints::transcript::SimulationTranscriptVar,
    iop::{bookkeeper::NameSpace, constraints::oracles::VirtualOracleVar, message::OracleIndex},
    iop_trace,
    prelude::{MsgRoundRef, ProverRoundMessageInfo},
};
use ark_crypto_primitives::merkle_tree::{constraints::ConfigGadget, Config};
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_r1cs_std::{
    fields::fp::FpVar,
    poly::domain::{vanishing_poly::VanishingPolynomial, Radix2DomainVar},
    prelude::*,
};
use ark_relations::r1cs::SynthesisError;
use ark_sponge::{
    constraints::{AbsorbGadget, SpongeWithGadget},
    Absorb,
};

#[derive(Debug, Clone)]
pub struct SumcheckPOracleVar<F: PrimeField> {
    pub summation_domain: Radix2CosetDomain<F>,

    pub claimed_sum: FpVar<F>,
    pub order_h_inv_times_claimed_sum: FpVar<F>,

    pub h_handle: (MsgRoundRef, OracleIndex),
    pub f_handle: (MsgRoundRef, OracleIndex),
}

impl<F: PrimeField> SumcheckPOracleVar<F> {
    pub fn new(
        summation_domain: Radix2CosetDomain<F>,
        claimed_sum: FpVar<F>,
        h_handle: (MsgRoundRef, OracleIndex),
        f_handle: (MsgRoundRef, OracleIndex),
    ) -> Self {
        let order_h_inv_times_claimed_sum =
            &claimed_sum * F::from(summation_domain.size() as u64).inverse().unwrap();
        Self {
            summation_domain,
            claimed_sum,
            order_h_inv_times_claimed_sum,
            h_handle,
            f_handle,
        }
    }
}

impl<F: PrimeField> VirtualOracleVar<F> for SumcheckPOracleVar<F> {
    fn constituent_oracle_handles(&self) -> Vec<(MsgRoundRef, Vec<OracleIndex>)> {
        vec![
            (self.h_handle.0, vec![self.h_handle.1]),
            (self.f_handle.0, vec![self.f_handle.1]),
        ]
    }

    fn evaluate_var(
        &self,
        coset_domain: Radix2DomainVar<F>,
        constituent_oracles: &[Vec<FpVar<F>>],
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        let h_eval = &constituent_oracles[0];
        let f_eval = &constituent_oracles[1];
        let mut cur_x_inv = coset_domain.offset().inverse().unwrap();

        let z_h = VanishingPolynomial::new(
            self.summation_domain.offset,
            self.summation_domain.dim() as u64,
        );
        let z_h_eval = coset_domain
            .elements()
            .into_iter()
            .map(|x| z_h.evaluate_constraints(&x))
            .collect::<Result<Vec<_>, SynthesisError>>()?;
        let gen_inv = coset_domain.gen.inverse().unwrap();
        assert_eq!(h_eval.len(), f_eval.len());
        assert_eq!(h_eval.len(), z_h_eval.len());
        assert_eq!(h_eval.len(), coset_domain.size() as usize);
        Ok(f_eval
            .iter()
            .zip(h_eval)
            .zip(z_h_eval)
            .map(|((f, h), z_h)| {
                let result = (f - &self.order_h_inv_times_claimed_sum - &z_h * h) * &cur_x_inv;
                cur_x_inv = &cur_x_inv * gen_inv;
                result
            })
            .collect())
    }
}

impl<F: PrimeField + Absorb> UnivariateSumcheck<F> {
    pub fn register_sumcheck_commit_phase_var<
        MT: Config,
        MTG: ConfigGadget<MT, F, Leaf = [FpVar<F>]>,
        S: SpongeWithGadget<F>,
    >(
        &self,
        transcript: &mut SimulationTranscriptVar<F, MT, MTG, S>,
        ns: NameSpace,
        f_handle: (MsgRoundRef, OracleIndex),
        claimed_sum: FpVar<F>,
    ) -> Result<(), SynthesisError>
    where
        MTG::InnerDigest: AbsorbGadget<F>,
        MT::InnerDigest: Absorb,
    {
        // receive h with no degree bound
        let round_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
            .with_num_message_oracles(1)
            .build();
        let h_handle =
            transcript.receive_prover_current_round(ns, round_info, iop_trace!("h oracle"))?;

        // register g as a virtual oracle
        let g_oracle = SumcheckPOracleVar::new(
            self.summation_domain,
            claimed_sum,
            (h_handle, (0, false).into()),
            f_handle,
        );
        let test_bound = self.degree_bound_of_g();
        transcript.register_prover_virtual_round(
            ns,
            g_oracle,
            vec![test_bound],
            vec![test_bound],
            iop_trace!("g oracle"),
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        protocol::tests::{FieldMTConfig, MockProtocol, MockProverParam, MockVerifierParam},
        test_util::poseidon_parameters,
        UnivariateSumcheck,
    };
    use ark_bcs::{
        bcs::{
            constraints::{
                proof::BCSProofVar, transcript::SimulationTranscriptVar,
                verifier::BCSVerifierGadget, MTHashParametersVar,
            },
            prover::BCSProof,
            MTHashParameters,
        },
        iop::{
            bookkeeper::NameSpace,
            constraints::{message::MessagesCollectionVar, IOPVerifierWithGadget},
            message::OracleIndex,
            ProverParam,
        },
        iop_trace,
        ldt::rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters},
        prelude::ProverRoundMessageInfo,
    };
    use ark_bls12_381::Fr;
    use ark_crypto_primitives::{
        crh::poseidon::constraints::CRHParametersVar,
        merkle_tree::{constraints::ConfigGadget, Config, IdentityDigestConverter},
    };
    use ark_ldt::domain::Radix2CosetDomain;
    use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial};
    use ark_r1cs_std::{
        alloc::{AllocVar, AllocationMode},
        fields::fp::FpVar,
    };
    use ark_relations::{
        ns,
        r1cs::{ConstraintSystem, ConstraintSystemRef, Namespace, SynthesisError},
    };
    use ark_sponge::{
        constraints::{AbsorbGadget, CryptographicSpongeVar, SpongeWithGadget},
        poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge},
        Absorb, CryptographicSponge,
    };
    use ark_std::{test_rng, vec};
    use core::borrow::Borrow;

    #[derive(Clone, Debug)]
    pub struct MockVerifierParamVar {
        pub summation_domain: Radix2CosetDomain<Fr>,
        pub claimed_sum: FpVar<Fr>,
    }

    impl AllocVar<MockVerifierParam, Fr> for MockVerifierParamVar {
        fn new_variable<T: Borrow<MockVerifierParam>>(
            cs: impl Into<Namespace<Fr>>,
            f: impl FnOnce() -> Result<T, SynthesisError>,
            mode: AllocationMode,
        ) -> Result<Self, SynthesisError> {
            let val = f()?;
            let val = val.borrow();
            let var = Self {
                summation_domain: val.summation_domain,
                claimed_sum: FpVar::new_variable(cs, || Ok(val.claimed_sum), mode)?,
            };
            Ok(var)
        }
    }

    impl<S: SpongeWithGadget<Fr>> IOPVerifierWithGadget<S, Fr> for MockProtocol {
        type VerifierParameterVar = MockVerifierParamVar;

        type VerifierOutputVar = ();
        type PublicInputVar = ();

        fn register_iop_structure_var<MT: Config, MTG: ConfigGadget<MT, Fr, Leaf = [FpVar<Fr>]>>(
            namespace: NameSpace,
            transcript: &mut SimulationTranscriptVar<Fr, MT, MTG, S>,
            verifier_parameter: &Self::VerifierParameterVar,
        ) -> Result<(), SynthesisError>
        where
            MT::InnerDigest: Absorb,
            MTG::InnerDigest: AbsorbGadget<Fr>,
        {
            let poly_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
                .with_num_message_oracles(1)
                .build();
            let poly_handle = transcript.receive_prover_current_round(
                namespace,
                poly_info,
                iop_trace!("poly to sum"),
            )?;
            let sumcheck = UnivariateSumcheck {
                summation_domain: verifier_parameter.summation_domain,
            };
            let sumcheck_ns = transcript.new_namespace(namespace, iop_trace!("sumcheck"));
            sumcheck.register_sumcheck_commit_phase_var(
                transcript,
                sumcheck_ns,
                (poly_handle, OracleIndex::new(0, false)),
                verifier_parameter.claimed_sum.clone(),
            )
        }

        fn query_and_decide_var<'a>(
            _cs: ConstraintSystemRef<Fr>,
            _namespace: NameSpace,
            _verifier_parameter: &Self::VerifierParameterVar,
            _public_input_var: &Self::PublicInputVar,
            _sponge: &mut S::Var,
            _transcript_messages: &mut MessagesCollectionVar<'a, Fr>,
        ) -> Result<Self::VerifierOutputVar, SynthesisError> {
            // nothing to do here. LDT is everything.
            Ok(())
        }
    }

    impl ConfigGadget<FieldMTConfig, Fr> for FieldMTConfig {
        type Leaf = [FpVar<Fr>];
        type LeafDigest = FpVar<Fr>;
        type LeafInnerConverter = IdentityDigestConverter<FpVar<Fr>>;
        type InnerDigest = FpVar<Fr>;
        type LeafHash = ark_crypto_primitives::crh::poseidon::constraints::CRHGadget<Fr>;
        type TwoToOneHash =
            ark_crypto_primitives::crh::poseidon::constraints::TwoToOneCRHGadget<Fr>;
    }

    #[test]
    fn test_constraints_end_to_end() {
        let mut rng = test_rng();
        let poseidon_param = poseidon_parameters();
        let sponge = PoseidonSponge::new(&poseidon_param);

        let codeword_domain = Radix2CosetDomain::new_radix2_coset(256, Fr::from(0x12345u128));
        let ldt_param = LinearCombinationLDTParameters::new(128, vec![1, 2, 1], codeword_domain, 5);
        let summation_domain = Radix2CosetDomain::new_radix2_coset(32, Fr::from(0x6789u128));

        let poly = DensePolynomial::rand(100, &mut rng);

        let claimed_sum = summation_domain.evaluate(&poly).into_iter().sum::<Fr>();

        let cs = ConstraintSystem::<Fr>::new_ref();

        let mt_hash_param = MTHashParameters::<FieldMTConfig> {
            leaf_hash_param: poseidon_param.clone(),
            inner_hash_param: poseidon_param.clone(),
        };

        let poseidon_param_var =
            CRHParametersVar::new_constant(cs.clone(), poseidon_parameters()).unwrap();

        let mt_hash_param_var = MTHashParametersVar::<Fr, FieldMTConfig, FieldMTConfig> {
            leaf_params: poseidon_param_var.clone(),
            inner_params: poseidon_param_var.clone(),
        };

        let prover_param = MockProverParam {
            summation_domain,
            poly,
            claimed_sum,
        };

        let verifier_param = prover_param.to_verifier_param();
        let verifier_param_var =
            MockVerifierParamVar::new_witness(ns!(cs, "verifier_param"), || Ok(verifier_param))
                .unwrap();

        let proof = BCSProof::generate::<MockProtocol, MockProtocol, LinearCombinationLDT<Fr>, _>(
            sponge.clone(),
            &(),
            &(),
            &prover_param,
            &ldt_param,
            mt_hash_param.clone(),
        )
        .unwrap();
        let proof_var = BCSProofVar::new_witness(ns!(cs, "proof"), || Ok(proof)).unwrap();

        let sponge_var = PoseidonSpongeVar::new(ns!(cs, "sponge").cs(), &poseidon_param);

        BCSVerifierGadget::verify::<MockProtocol, LinearCombinationLDT<Fr>, PoseidonSponge<Fr>>(
            cs.clone(),
            sponge_var,
            &proof_var,
            &(),
            &verifier_param_var,
            &ldt_param,
            &mt_hash_param_var,
        )
        .unwrap();
    }
}
