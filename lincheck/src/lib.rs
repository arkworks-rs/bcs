#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;
extern crate core;

pub mod matrix;

use crate::matrix::{Matrix, NativeMatrixSpec};
use ark_bcs::{
    bcs::transcript::LDTInfo,
    iop::{bookkeeper::NameSpace, message::OracleIndex, oracles::VirtualOracle},
    iop_trace,
    prelude::*,
};
use ark_ff::PrimeField;

use ark_ldt::domain::Radix2CosetDomain;
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize::Full};
use ark_std::{vec, vec::Vec};
use ark_uni_sumcheck::UnivariateSumcheck;

/// Lincheck Protocol
/// We want to prove f_Mz = Mf_z where f_Mz and f_z is an RS code under codeword
/// domain, where f_Mz extends to `constraint_domain`, and f_z extends to
/// `variable_domain`.
///
/// M is a matrix of shape `constraint_domain.size()` x
/// `variable_domain.size()`.
pub struct Lincheck<F: PrimeField + Absorb> {
    pub constraint_domain: Radix2CosetDomain<F>,
    pub variable_domain: Radix2CosetDomain<F>,
}

/// virtual oracle for lincheck
pub struct LincheckVO<F: PrimeField> {
    pub constraint_domain: Radix2CosetDomain<F>,
    pub variable_domain: Radix2CosetDomain<F>,
    pub codeword_domain: Radix2CosetDomain<F>,
    /// r on constraint domain
    pub rx: Vec<F>,
    /// M^T r on variable domain
    pub mtrx: Vec<F>,
    pub fmz_handle: (MsgRoundRef, OracleIndex),
    pub fz_handle: (MsgRoundRef, OracleIndex),
}

impl<F: PrimeField> VirtualOracle<F> for LincheckVO<F> {
    fn constituent_oracle_handles(&self) -> Vec<(MsgRoundRef, Vec<OracleIndex>)> {
        vec![
            (self.fmz_handle.0, vec![self.fmz_handle.1]),
            (self.fz_handle.0, vec![self.fz_handle.1]),
        ]
    }

    fn local_constituent_oracles(&self) -> Vec<Vec<F>> {
        // in this context we assume variable domain is a subset of constraint domain
        // check if this is true
        // h1 is constraint domain, h2 is variable domain
        assert!(self.constraint_domain.size() >= self.variable_domain.size());
        let (h2_positions_in_h1, expected_variable_domain) = self
            .constraint_domain
            .query_position_to_coset(0, self.variable_domain.dim());
        assert_eq!(expected_variable_domain, self.variable_domain);

        // summation domain = H_1 U H_2 = H_1 because H_2 is a subset of H_1
        let summation_domain = self.constraint_domain;
        let rx_cd = self
            .codeword_domain
            .evaluate(&self.constraint_domain.interpolate(self.rx.clone()));
        // for mtrx, we need to make sure the local oracle evaluates to zero at H1 - H2
        assert_eq!(h2_positions_in_h1.len(), self.mtrx.len());
        let mut mtrx_on_h1 = (0..summation_domain.size())
            .map(|_| F::zero())
            .collect::<Vec<_>>();
        for (i, x) in h2_positions_in_h1.iter().zip(self.mtrx.iter()) {
            mtrx_on_h1[*i] = *x;
        }
        let mtrx = self
            .codeword_domain
            .evaluate(&summation_domain.interpolate(mtrx_on_h1));
        vec![rx_cd, mtrx]
    }

    fn evaluate(
        &self,
        _coset_domain: Radix2CosetDomain<F>,
        constituent_oracles: &[Vec<F>],
    ) -> Vec<F> {
        let f_mz = &constituent_oracles[0];
        let f_z = &constituent_oracles[1];
        let r = &constituent_oracles[2];
        let mtr = &constituent_oracles[3];
        // let vd_vp = self.variable_domain_vp.evaluation_over_coset(&coset_domain);

        // make sure those four oracles have same length
        assert_eq!(f_mz.len(), f_z.len());
        assert_eq!(f_mz.len(), r.len());
        assert_eq!(f_mz.len(), mtr.len());
        // assert_eq!(f_mz.len(), vd_vp.len());

        let mut h = Vec::with_capacity(f_mz.len());
        for i in 0..f_mz.len() {
            h.push(r[i] * f_mz[i] - mtr[i] * f_z[i]);
        }
        h
    }
}

impl<F: PrimeField + Absorb> Lincheck<F> {
    fn calculate_rx(&self, alpha: F) -> Vec<F> {
        // calculate `r(x)` of size `constraint_domain.size()`, which is [1, alpha,
        // alpha^2, ..., alpha^(constraint_domain.size()-1)]
        let mut rx = Vec::with_capacity(self.constraint_domain.size());
        rx.push(F::one());
        for _ in 1..self.constraint_domain.size() {
            rx.push(*rx.last().unwrap() * alpha);
        }
        rx
    }

    /// Send prover message to the transcript.
    /// `z`: witness `z` in linear relation `Mz = M @ z`
    /// `f_z_oracle`: an oracle on `codeword_domain` of interpolation polynomial
    /// of `z` as evaluation on `variable_domain` `mz`: `Mz` in linear
    /// relation `Mz = M @ z` `f_mz_oracle`: an oracle on `codeword_domain`
    /// of interpolation polynomial of `mz` as evaluation on `constraint_domain`
    /// `mat`: Matrix where f_Mz = mat @ f_z, using extension of both oracles
    pub fn prove<P: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        &self,
        ns: NameSpace,
        transcript: &mut Transcript<P, S, F>,
        f_z_oracle: (MsgRoundRef, OracleIndex),
        f_mz_oracle: (MsgRoundRef, OracleIndex),
        mat: &Matrix<NativeMatrixSpec<F>>,
    ) where
        P::InnerDigest: Absorb,
    {
        assert!(
            f_z_oracle.1.bounded,
            "f_z must be low degree and has degree bound"
        );
        let fz_degree_bound = transcript
            .get_previously_sent_prover_round_info(f_z_oracle.0)
            .reed_solomon_code_degree_bound[f_z_oracle.1.idx];

        // matrix shape sanity check
        assert_eq!(mat.num_rows(), self.constraint_domain.size());
        assert_eq!(mat.num_cols(), self.variable_domain.size());
        // for now, we assume that `self.variable_domain` is smaller than
        // `self.constraint_domain` (indeed, it should be a subset, and that is
        // checked in virtual oracle)
        assert!(self.variable_domain.size() < self.constraint_domain.size());

        let codeword_domain = transcript.codeword_domain();

        // receive alpha from verifier
        let alpha = transcript.squeeze_verifier_field_elements(&[Full])[0];
        transcript.submit_verifier_current_round(ns, iop_trace!("alpha"));

        let virtual_oracle_degree_bound = self.constraint_domain.size() + fz_degree_bound;
        let rx = self.calculate_rx(alpha); // r on constraint domain

        let mtrx = mat.transpose().mul_vector(&rx); // mt_rx on variable domain

        let vo = LincheckVO {
            codeword_domain,
            constraint_domain: self.constraint_domain,
            variable_domain: self.variable_domain,
            rx,
            mtrx,
            fmz_handle: f_mz_oracle,
            fz_handle: f_z_oracle,
        };

        let lincheck_vo = transcript.register_prover_virtual_round(
            ns,
            vo,
            vec![virtual_oracle_degree_bound],
            vec![virtual_oracle_degree_bound],
            iop_trace!("Lincheck virtual_oracle"),
        );


        let lincheck_vo_cd = transcript
            .get_previous_sent_prover_rs_codes(lincheck_vo)
            .pop()
            .unwrap();
        let lincheck_vo_coeff = codeword_domain.interpolate(lincheck_vo_cd);


        // sanity check: lincheck_vo evaluated at constraint domain sum to 0
        if cfg!(debug_assertions) {
            let rs_codes_eval = self.constraint_domain.evaluate(&lincheck_vo_coeff);
            let actual_sum = rs_codes_eval.iter().sum::<F>();
            assert_eq!(actual_sum, F::zero(), "virtual oracle does not sum to 0 at constraint domain. relation Mz = M @ z is not satisfied");
        };

        // invoke sumcheck on this vo
        let uni_sumcheck = UnivariateSumcheck::new(self.constraint_domain);

        // sumcheck protocol on constraint domain
        let sumcheck_ns = transcript.new_namespace(ns, iop_trace!("sumcheck"));
        uni_sumcheck.prove(
            transcript,
            sumcheck_ns,
            &lincheck_vo_coeff,
            (lincheck_vo, (0, true).into()),
            F::zero(),
        );
    }

    pub fn register<P: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        &self,
        ns: NameSpace,
        transcript: &mut SimulationTranscript<P, S, F>,
        f_z: (MsgRoundRef, OracleIndex),
        f_mz: (MsgRoundRef, OracleIndex),
        fz_degree_bound: usize,
        mat: &Matrix<NativeMatrixSpec<F>>,
    ) where
        P::InnerDigest: Absorb,
    {
        assert!(f_z.1.bounded, "f_z must be low degree and has degree bound");
        // matrix shape sanity check
        assert_eq!(mat.num_rows(), self.constraint_domain.size());
        assert_eq!(mat.num_cols(), self.variable_domain.size());
        // for now, we assume that `self.variable_domain` is smaller than
        // `self.constraint_domain` (indeed, it should be a subset, and that is
        // checked in virtual oracle)
        assert!(self.variable_domain.size() < self.constraint_domain.size());

        let codeword_domain = transcript.codeword_domain();

        // sample alpha
        let alpha = transcript
            .squeeze_verifier_field_elements(&[Full])
            .pop()
            .unwrap();

        transcript.submit_verifier_current_round(ns, iop_trace!("alpha")); // TODO: we can remove the entire `submit` call in ark-bcs

        let virtual_oracle_degree_bound = self.constraint_domain.size() + fz_degree_bound;

        let r = self.calculate_rx(alpha); // r on constraint domain

        let mt_rx = mat.transpose().mul_vector(&r); // mt_rx on variable domain

        let vo = LincheckVO {
            codeword_domain,
            constraint_domain: self.constraint_domain,
            variable_domain: self.variable_domain,
            rx: r,
            mtrx: mt_rx,
            fmz_handle: f_mz,
            fz_handle: f_z,
        };

        let lincheck_vo = transcript.register_prover_virtual_round(
            ns,
            vo,
            vec![virtual_oracle_degree_bound],
            vec![virtual_oracle_degree_bound],
            iop_trace!("Lincheck virtual_oracle"),
        );

        let uni_sumcheck = UnivariateSumcheck::new(self.constraint_domain);

        // sumcheck protocol on constraint domain
        let sumcheck_ns = transcript.new_namespace(ns, iop_trace!("sumcheck"));
        uni_sumcheck.register(
            transcript,
            sumcheck_ns,
            (lincheck_vo, (0, true).into()),
            F::zero(),
        )
    }

    // lincheck is just a mapping reduction to sumcheck and does not have any query
    // phase or post-processing
}

#[cfg(test)]
mod tests {
    use crate::{Lincheck, LincheckVO, Matrix, NativeMatrixSpec};
    use alloc::vec::Vec;
    use ark_bcs::{
        iop::oracles::{RoundOracle, VirtualOracle},
        prelude::{
            MessagesCollection, MsgRoundRef, ProverRoundMessageInfo, SimulationTranscript,
            Transcript,
        },
    };
    use ark_bls12_381::Fr;
    use ark_crypto_primitives::{
        crh::poseidon,
        merkle_tree::{Config, IdentityDigestConverter},
    };
    use ark_ff::{field_new, FpParameters, PrimeField};
    use ark_ldt::domain::Radix2CosetDomain;

    use ark_poly::Polynomial;
    use ark_sponge::{
        poseidon::{find_poseidon_ark_and_mds, PoseidonParameters, PoseidonSponge},
        Absorb, CryptographicSponge,
    };
    use ark_std::{test_rng, One, UniformRand, Zero};

    use ark_bcs::{
        bcs::{prover::BCSProof, transcript::LDTInfo, verifier::BCSVerifier, MTHashParameters},
        iop::{bookkeeper::NameSpace, prover::IOPProver, verifier::IOPVerifier, ProverParam},
        iop_trace,
        ldt::rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters},
        Error,
    };

    #[test]
    fn test_vo() {
        let mut rng = test_rng();
        let log_num_constraints = 10;
        let log_num_variables = 8;
        let num_constraints = 1 << log_num_constraints;
        let num_variables = 1 << log_num_variables;
        let constraint_domain = Radix2CosetDomain::new_radix2_coset(num_constraints, Fr::one());
        let variable_domain =
            constraint_domain.fold((log_num_constraints - log_num_variables) as u64);
        let codeword_domain = Radix2CosetDomain::new_radix2_coset(1 << 12, Fr::rand(&mut rng));
        assert_eq!(variable_domain.size(), num_variables);

        let mat = Matrix::<NativeMatrixSpec<_>>::new(
            (0..num_constraints)
                .map(|_| {
                    (0..num_variables)
                        .map(|_| Fr::rand(&mut rng))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>(),
        );

        let mat_t = mat.transpose();

        let z = (0..num_variables)
            .map(|_| Fr::rand(&mut rng))
            .collect::<Vec<_>>();
        let mz = mat.mul_vector(&z);
        let f_z = codeword_domain.evaluate(&variable_domain.interpolate(z.clone()));
        let f_mz = codeword_domain.evaluate(&constraint_domain.interpolate(mz.clone()));

        let lincheck = Lincheck {
            constraint_domain,
            variable_domain,
        };

        let alpha = Fr::rand(&mut rng);

        let rx = lincheck.calculate_rx(alpha); // on constraint domain
        let mtrx = mat_t.mul_vector(&rx); // on variable domain

        // check individual sums
        assert_eq!(mtrx.len(), z.len());
        assert_eq!(mtrx.len(), variable_domain.size());
        let sum1 = mtrx.iter().zip(z.iter()).map(|(a, b)| *a * *b).sum::<Fr>();

        assert_eq!(rx.len(), mz.len());
        assert_eq!(rx.len(), constraint_domain.size());
        let sum2 = rx.iter().zip(mz.iter()).map(|(a, b)| *a * *b).sum::<Fr>();

        assert_eq!(sum1, sum2);

        let vo = LincheckVO {
            codeword_domain,
            constraint_domain,
            variable_domain,
            rx,
            mtrx,
            fmz_handle: (MsgRoundRef::default(), (0, false).into()),
            fz_handle: (MsgRoundRef::default(), (0, false).into()),
        };

        let local_oracles = vo.local_constituent_oracles();

        let eval_of_vo_on_codeword_domain = vo.evaluate(
            codeword_domain,
            &[
                f_mz.clone(),
                f_z.clone(),
                local_oracles[0].clone(),
                local_oracles[1].clone(),
            ],
        );

        let f_mz_degree = { codeword_domain.interpolate(f_mz).degree() };
        let f_z_degree = { codeword_domain.interpolate(f_z).degree() };
        let deg_bound = ark_std::cmp::max(f_mz_degree, f_z_degree);

        // check degree
        let vo_poly = codeword_domain.interpolate(eval_of_vo_on_codeword_domain.clone());
        println!(
            "degree of vo_poly: {}, degree bound: {}, codeword_domain size: {}",
            vo_poly.degree(),
            deg_bound + constraint_domain.size(),
            codeword_domain.size()
        );
        assert!(vo_poly.degree() <= deg_bound + constraint_domain.size());

        // constraint domain is summation domain
        let eval_of_vo_on_constraint_domain =
            constraint_domain.evaluate(&codeword_domain.interpolate(eval_of_vo_on_codeword_domain));

        let sum_of_vo_on_constraint_domain = eval_of_vo_on_constraint_domain.iter().sum::<Fr>();
        assert_eq!(sum_of_vo_on_constraint_domain, Fr::zero());
    }

    pub(crate) struct MockProtocol;

    #[derive(Clone, Debug)]
    pub(crate) struct MockProverParam {
        constraint_domain: Radix2CosetDomain<Fr>,
        variable_domain: Radix2CosetDomain<Fr>,
        mz: Vec<Fr>,
        z: Vec<Fr>,
        z_bound: usize,
        mat: Matrix<NativeMatrixSpec<Fr>>,
    }

    #[derive(Clone, Debug)]
    pub(crate) struct MockVerifierParam {
        constraint_domain: Radix2CosetDomain<Fr>,
        variable_domain: Radix2CosetDomain<Fr>,
        deg_bound: usize,
        mat: Matrix<NativeMatrixSpec<Fr>>,
    }

    impl ProverParam for MockProverParam {
        type VerifierParameter = MockVerifierParam;

        fn to_verifier_param(&self) -> Self::VerifierParameter {
            MockVerifierParam {
                constraint_domain: self.constraint_domain,
                variable_domain: self.variable_domain,
                deg_bound: self.z_bound,
                mat: self.mat.clone(),
            }
        }
    }

    impl IOPProver<Fr> for MockProtocol {
        type ProverParameter = MockProverParam;
        type PublicInput = ();
        type PrivateInput = ();

        fn prove<MT: Config<Leaf = [Fr]>, S: CryptographicSponge>(
            ns: NameSpace,
            public_input: &Self::PublicInput,
            private_input: &Self::PrivateInput,
            transcript: &mut Transcript<MT, S, Fr>,
            prover_parameter: &Self::ProverParameter,
        ) -> Result<(), Error>
        where
            MT::InnerDigest: Absorb,
        {
            let pp = prover_parameter;
            let _ = (public_input, private_input);
            let codeword_domain = transcript.codeword_domain();
            assert!(
                codeword_domain.size() > pp.constraint_domain.size(),
                "codeword domain too small"
            );
            assert!(
                codeword_domain.size() > pp.variable_domain.size(),
                "codeword domain too small"
            );
            // send z and mz
            let z = &prover_parameter.z;
            let mz = &prover_parameter.mz;

            let f_z = codeword_domain.evaluate(&pp.variable_domain.interpolate(z.clone()));
            let f_mz = codeword_domain.evaluate(&pp.constraint_domain.interpolate(mz.clone()));

            let f_z_round = transcript
                .add_prover_round_with_codeword_domain()
                .send_oracle_evaluations_with_degree_bound(f_z, pp.z_bound)
                .submit(ns, iop_trace!("f_z"))?;

            let f_mz_round = transcript
                .add_prover_round_with_codeword_domain()
                .send_oracle_message_without_degree_bound(f_mz)
                .submit(ns, iop_trace!("f_mz"))?;

            let lincheck = Lincheck {
                variable_domain: pp.variable_domain,
                constraint_domain: pp.constraint_domain,
            };
            let lincheck_ns = transcript.new_namespace(ns, iop_trace!("lincheck"));
            lincheck.prove(
                lincheck_ns,
                transcript,
                (f_z_round, (0, true).into()),
                (f_mz_round, (0, false).into()),
                &pp.mat,
            );

            Ok(())
        }
    }

    impl<S: CryptographicSponge> IOPVerifier<S, Fr> for MockProtocol {
        type VerifierOutput = ();
        type VerifierParameter = MockVerifierParam;
        type PublicInput = ();

        fn register_iop_structure<MT: Config<Leaf = [Fr]>>(
            ns: NameSpace,
            transcript: &mut SimulationTranscript<MT, S, Fr>,
            verifier_parameter: &Self::VerifierParameter,
        ) where
            MT::InnerDigest: Absorb,
        {
            let vp = verifier_parameter;
            let codeword_domain = transcript.codeword_domain();
            assert!(
                codeword_domain.size() > vp.constraint_domain.size(),
                "codeword domain too small"
            );
            assert!(
                codeword_domain.size() > vp.variable_domain.size(),
                "codeword domain too small"
            );
            // receive z and mz
            let expected_z_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
                .with_reed_solomon_codes_degree_bounds(vec![vp.deg_bound])
                .build();

            let expected_mz_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
                .with_num_message_oracles(1)
                .build();

            let f_z_round =
                transcript.receive_prover_current_round(ns, expected_z_info, iop_trace!("f_z"));
            let f_mz_round =
                transcript.receive_prover_current_round(ns, expected_mz_info, iop_trace!("f_mz"));

            let lincheck = Lincheck {
                variable_domain: vp.variable_domain,
                constraint_domain: vp.constraint_domain,
            };
            let lincheck_ns = transcript.new_namespace(ns, iop_trace!("lincheck"));
            lincheck.register(
                lincheck_ns,
                transcript,
                (f_z_round, (0, true).into()),
                (f_mz_round, (0, false).into()),
                vp.deg_bound,
                &vp.mat,
            );
        }

        fn query_and_decide<O: RoundOracle<Fr>>(
            namespace: NameSpace,
            verifier_parameter: &Self::VerifierParameter,
            public_input: &Self::PublicInput,
            sponge: &mut S,
            transcript_messages: &mut MessagesCollection<Fr, O>,
        ) -> Result<Self::VerifierOutput, Error> {
            let _ = (
                namespace,
                verifier_parameter,
                public_input,
                sponge,
                transcript_messages,
            );
            Ok(())
        }
    }

    pub(crate) struct FieldMTConfig;

    pub(crate) type H = poseidon::CRH<Fr>;
    pub(crate) type TwoToOneH = poseidon::TwoToOneCRH<Fr>;

    impl Config for FieldMTConfig {
        type Leaf = [Fr];
        type LeafDigest = Fr;
        type LeafInnerDigestConverter = IdentityDigestConverter<Fr>;
        type InnerDigest = Fr;
        type LeafHash = H;
        type TwoToOneHash = TwoToOneH;
    }

    #[test]
    fn test_lincheck_end_to_end() {
        let mut rng = test_rng();

        const CONSTRAINT_DOMAIN_SIZE: usize = 128;
        const VARIABLE_DOMAIN_SIZE: usize = CONSTRAINT_DOMAIN_SIZE >> 1;
        let constraint_domain =
            Radix2CosetDomain::new_radix2_coset(CONSTRAINT_DOMAIN_SIZE, Fr::rand(&mut rng));
        let variable_domain = constraint_domain.fold(1);

        let z = (0..VARIABLE_DOMAIN_SIZE)
            .map(|_| Fr::rand(&mut rng))
            .collect::<Vec<_>>();

        let mat = (0..CONSTRAINT_DOMAIN_SIZE)
            .map(|_| {
                (0..VARIABLE_DOMAIN_SIZE)
                    .map(|_| Fr::rand(&mut rng))
                    .collect::<Vec<_>>()
            })
            .collect::<Matrix<NativeMatrixSpec<Fr>>>();
        let mz = mat.mul_vector(&z);

        let deg_z = variable_domain.interpolate(z.clone()).degree();
        let deg_mz = constraint_domain.interpolate(mz.clone()).degree();

        let pp = MockProverParam {
            constraint_domain,
            variable_domain,
            mat,
            z,
            mz,
            z_bound: ark_std::cmp::max(deg_z, deg_mz),
        };
        let vp = pp.to_verifier_param();

        let sponge = PoseidonSponge::new(&poseidon_parameters());

        let codeword_domain = Radix2CosetDomain::new_radix2_coset(1024, field_new!(Fr, "12345"));
        let ldt_param = LinearCombinationLDTParameters::new(512, vec![1, 2, 1], codeword_domain, 5);

        let mt_hash_param = MTHashParameters::<FieldMTConfig> {
            leaf_hash_param: poseidon_parameters(),
            inner_hash_param: poseidon_parameters(),
        };

        let proof = BCSProof::generate::<MockProtocol, MockProtocol, LinearCombinationLDT<Fr>, _>(
            sponge.clone(),
            &(),
            &(),
            &pp,
            &ldt_param,
            mt_hash_param.clone(),
        )
        .unwrap();

        BCSVerifier::verify::<MockProtocol, LinearCombinationLDT<Fr>, _>(
            sponge,
            &proof,
            &(),
            &vp,
            &ldt_param,
            mt_hash_param,
        )
        .unwrap();

    }

    pub(crate) fn poseidon_parameters() -> PoseidonParameters<Fr> {
        let full_rounds = 8;
        let partial_rounds = 31;
        let alpha = 5;
        let rate = 2;

        let (ark, mds) = find_poseidon_ark_and_mds::<Fr>(
            <Fr as PrimeField>::Params::MODULUS_BITS as u64,
            rate,
            full_rounds,
            partial_rounds,
            0,
        );

        PoseidonParameters::new(
            full_rounds as usize,
            partial_rounds as usize,
            alpha,
            mds,
            ark,
            rate,
            1,
        )
    }
}
