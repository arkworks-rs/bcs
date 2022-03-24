#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;
extern crate core;

pub mod matrix;

use crate::matrix::{Matrix, NativeMatrixSpec};
use ark_bcs::bcs::transcript::LDTInfo;
use ark_bcs::iop::bookkeeper::NameSpace;
use ark_bcs::iop::message::OracleIndex;
use ark_bcs::iop::oracles::VirtualOracle;
use ark_bcs::iop_trace;
use ark_bcs::prelude::*;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_sponge::FieldElementSize::Full;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_std::vec;
use ark_std::vec::Vec;
use ark_uni_sumcheck::UnivariateSumcheck;

/// Lincheck Protocol
/// We want to prove f_Mz = Mf_z where f_Mz and f_z is an RS code under codeword domain,
/// where f_Mz extends to `constraint_domain`, and f_z extends to `variable_domain`.
///
/// M is a matrix of shape `constraint_domain.size()` x `variable_domain.size()`.
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
        let (h2_positions_in_h1, expected_variable_domain) = self.constraint_domain.query_position_to_coset(0, self.variable_domain.dim());
        assert_eq!(expected_variable_domain, self.variable_domain);

        // summation domain = H_1 U H_2 = H_1 because H_2 is a subset of H_1
        let summation_domain = self.constraint_domain;
        let rx_cd = self.codeword_domain.evaluate(&self.constraint_domain.interpolate(self.rx.clone()));
        // for mtrx, we need to make sure the local oracle evaluates to zero at H1 - H2
        assert_eq!(h2_positions_in_h1.len(), self.mtrx.len());
        let mut mtrx_on_h1 = (0..summation_domain.size()).map(|_| F::zero()).collect::<Vec<_>>();
        for (i,x) in h2_positions_in_h1.iter().zip(self.mtrx.iter()){
            mtrx_on_h1[*i] = *x;
        }
        let mtrx = self.codeword_domain.evaluate(&summation_domain.interpolate(mtrx_on_h1));
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
        // calculate `r(x)` of size `constraint_domain.size()`, which is [1, alpha, alpha^2, ..., alpha^(constraint_domain.size()-1)]
        let mut rx = Vec::with_capacity(self.constraint_domain.size());
        rx.push(F::one());
        for _ in 1..self.constraint_domain.size() {
            rx.push(*rx.last().unwrap() * alpha);
        }
        rx
    }

    /// Send prover message to the transcript.
    /// `f_Mz`: an oracle handle of f_Mz
    /// `f_z`: f_z
    /// `mat`: Matrix where f_Mz = mat * f_z, using extension of both oracles
    pub fn prove<P: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        &self,
        ns: NameSpace,
        transcript: &mut Transcript<P, S, F>,
        f_z: (MsgRoundRef, OracleIndex),
        mat: &Matrix<NativeMatrixSpec<F>>,
    ) where
        P::InnerDigest: Absorb,
    {
        assert!(f_z.1.bounded, "f_z must be low degree and has degree bound");
        let fz_degree_bound = transcript
            .get_previously_sent_prover_round_info(f_z.0)
            .reed_solomon_code_degree_bound[f_z.1.idx];

        // matrix shape sanity check
        assert_eq!(mat.num_rows(), self.constraint_domain.size());
        assert_eq!(mat.num_cols(), self.variable_domain.size());

        let codeword_domain = transcript.codeword_domain();

        // receive alpha from verifier
        let alpha = transcript.squeeze_verifier_field_elements(&[Full])[0];

        // LDE f_z to match the size of `variable_domain`
        let f_z_cd = transcript.get_previously_sent_prover_oracle(f_z.0, f_z.1);
        let f_z_coeff = transcript.codeword_domain().interpolate(f_z_cd.to_vec());
        let f_z_vd = self.variable_domain.evaluate(&f_z_coeff);

        // calculate f_Mz on constraint domain, and extend it to codeword domain
        // TODO; f_Mz maybe calculated elsewhere because we need to prove this relation
        let f_mz_cd = mat.mul_vector(&f_z_vd);
        let f_mz_coeff = self.constraint_domain.interpolate(f_mz_cd);
        // send f_Mz oracle
        // we do not need to do LDT for f_Mz, since f_z is already low-degree. f_Mz(x) = M<coeff, [1, x, x^2, ..., x^{deg-1}]> = <M@coeff, [1, x, x^2, ..., x^{deg-1}]>
        // so degree of f_mz is upper bounded by deg(f_z)
        let f_mz_handle = transcript
            .add_prover_round_with_codeword_domain()
            .send_oracle_message_without_degree_bound(codeword_domain.evaluate(&f_mz_coeff))
            .submit(ns, iop_trace!("f_Mz"))
            .unwrap();

        let virtual_oracle_degree_bound = self.constraint_domain.size() + fz_degree_bound; // TODO: I think we can use variable_domain.size() instead of constraint_domain.size()?

        let r = self.calculate_rx(alpha); // r on constraint domain

        let mt_rx = mat.mul_vector(&r); // mt_rx on variable domain

        let vo = LincheckVO {
            codeword_domain,
            constraint_domain: self.constraint_domain,
            variable_domain: self.variable_domain,
            rx: r,
            mtrx: mt_rx,
            fmz_handle: (f_mz_handle, (0, false).into()),
            fz_handle: f_z,
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

        // invoke sumcheck on this vo
        let uni_sumcheck = UnivariateSumcheck::new(self.constraint_domain); // check this

        // sanity check: lincheck_vo evaluated at constraint domain sum to 0
        if cfg!(debug_assertions) {
            let rs_codes_eval = self.constraint_domain.evaluate(&lincheck_vo_coeff);
            let actual_sum = rs_codes_eval.iter().sum::<F>();
            assert_eq!(actual_sum, F::zero());
        } else {
            todo!("remove me")
        };

        // sumcheck protocol on constraint domain
        let sumcheck_ns = transcript.new_namespace(ns, iop_trace!("sumcheck"));
        uni_sumcheck.send_sumcheck_prover_message(
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
        fz_degree_bound: usize, // TODO: allow transcript to get this degree bound
        mat: &Matrix<NativeMatrixSpec<F>>,
    ) where
        P::InnerDigest: Absorb,
    {
        assert!(f_z.1.bounded, "f_z must be low degree and has degree bound");
        // matrix shape sanity check
        assert_eq!(mat.num_rows(), self.constraint_domain.size());
        assert_eq!(mat.num_cols(), self.variable_domain.size());

        let codeword_domain = transcript.codeword_domain();

        // sample alpha
        let alpha = transcript
            .squeeze_verifier_field_elements(&[Full])
            .pop()
            .unwrap();

        // get f_mz
        let f_mz_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
            .with_num_message_oracles(1)
            .build();
        let f_mz_handle =
            transcript.receive_prover_current_round(ns, f_mz_info, iop_trace!("f_Mz"));

        let virtual_oracle_degree_bound = self.constraint_domain.size() + fz_degree_bound;

        let r = self.calculate_rx(alpha); // r on constraint domain

        let mt_rx = mat.mul_vector(&r); // mt_rx on variable domain

        let vo = LincheckVO {
            codeword_domain,
            constraint_domain: self.constraint_domain,
            variable_domain: self.variable_domain,
            rx: r,
            mtrx: mt_rx,
            fmz_handle: (f_mz_handle, (0, false).into()),
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
        uni_sumcheck.register_sumcheck_commit_phase(
            transcript,
            sumcheck_ns,
            (lincheck_vo, (0, true).into()),
            F::zero(),
        )
    }

    // lincheck is just a mapping reduction to sumcheck and does not have any query phase or post-processing
}

#[cfg(test)]
mod tests {
    use crate::{Lincheck, LincheckVO, Matrix, NativeMatrixSpec};
    use alloc::vec::Vec;
    use ark_bcs::iop::oracles::VirtualOracle;
    use ark_bcs::prelude::MsgRoundRef;
    use ark_bls12_381::Fr;
    use ark_ldt::domain::Radix2CosetDomain;
    use ark_std::{test_rng, One, UniformRand, Zero};

    #[test]
    fn test_vo() {
        let mut rng = test_rng();
        let log_num_constraints = 10;
        let log_num_variables = 8;
        let num_constraints = 1 << log_num_constraints;
        let num_variables = 1 << log_num_variables;
        let constraint_domain = Radix2CosetDomain::new_radix2_coset(num_constraints, Fr::one());
        let variable_domain = constraint_domain.fold((log_num_constraints - log_num_variables) as u64);
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
        let sum1 = mtrx.iter().zip(z.iter()).map(|(a,b)|*a * *b).sum::<Fr>();

        assert_eq!(rx.len(), mz.len());
        assert_eq!(rx.len(), constraint_domain.size());
        let sum2 = rx.iter().zip(mz.iter()).map(|(a,b)|*a * *b).sum::<Fr>();

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

        let eval_of_vo_on_codeword_domain =  vo.evaluate(
            codeword_domain,
            &[
                f_mz,
                f_z,
                local_oracles[0].clone(),
                local_oracles[1].clone(),
            ],
        );

        // constraint domain is summation domain
        let eval_of_vo_on_constraint_domain = constraint_domain.evaluate(&codeword_domain.interpolate(eval_of_vo_on_codeword_domain));

        let sum_of_vo_on_constraint_domain = eval_of_vo_on_constraint_domain.iter().sum::<Fr>();
        assert_eq!(sum_of_vo_on_constraint_domain, Fr::zero());
    }
}
