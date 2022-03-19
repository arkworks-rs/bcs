#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

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
    pub codeword_domain: Radix2CosetDomain<F>,
    /// evaluation of r(x) on codeword domain
    pub rx_eval_cd: Vec<F>,
    pub mrx_eval_cd: Vec<F>,
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
        vec![self.rx_eval_cd.clone(), self.mrx_eval_cd.clone()]
    }

    fn evaluate(
        &self,
        _coset_domain: Radix2CosetDomain<F>,
        constituent_oracles: &[Vec<F>],
    ) -> Vec<F> {
        let f_mz = &constituent_oracles[0];
        let f_z = &constituent_oracles[1];
        let r = &constituent_oracles[2];
        let mr = &constituent_oracles[3];

        // make sure those four oracles have same length
        assert_eq!(f_mz.len(), f_z.len());
        assert_eq!(f_mz.len(), r.len());
        assert_eq!(f_mz.len(), mr.len());

        let mut h = Vec::with_capacity(f_mz.len());
        for i in 0..f_mz.len() {
            h[i] = r[i] * f_mz[i] - mr[i] * f_z[i];
        }
        h
    }
}

impl<F: PrimeField + Absorb> Lincheck<F> {
    fn calculate_rx(&self, alpha: F) -> Vec<F> {
        // calculate `r(x)` of size `variable_domain.size()`, which is [1, alpha, alpha^2, ..., alpha^(variable_domain.size()-1)]
        let mut rx = Vec::with_capacity(self.variable_domain.size());
        rx.push(F::one());
        for _ in 1..self.variable_domain.size() {
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

        let r_x_vd = self.calculate_rx(alpha); // r_x on variable domain
        let r_x_cd = codeword_domain.evaluate(&self.variable_domain.interpolate(r_x_vd.clone())); // r_x on codeword domain

        let m_rx_vd = mat.mul_vector(&r_x_vd); // m_rx on variable domain
        let m_rx_cd = codeword_domain.evaluate(&self.variable_domain.interpolate(m_rx_vd.clone())); // m_rx on codeword domain

        let vo = LincheckVO {
            codeword_domain,
            rx_eval_cd: r_x_cd,
            mrx_eval_cd: m_rx_cd,
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
        let alpha = transcript.squeeze_verifier_field_elements(&[Full]).pop().unwrap();

        // get f_mz
        let f_mz_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
            .with_num_message_oracles(1)
            .build();
        let f_mz_handle = transcript.receive_prover_current_round(ns, f_mz_info, iop_trace!("f_Mz"));

        let virtual_oracle_degree_bound = self.constraint_domain.size() + fz_degree_bound;

        let r_x_vd = self.calculate_rx(alpha); // r_x on variable domain
        let r_x_cd = codeword_domain.evaluate(&self.variable_domain.interpolate(r_x_vd.clone())); // r_x on codeword domain

        let m_rx_vd = mat.mul_vector(&r_x_vd); // m_rx on variable domain
        let m_rx_cd = codeword_domain.evaluate(&self.variable_domain.interpolate(m_rx_vd.clone())); // m_rx on codeword domain

        let vo = LincheckVO {
            codeword_domain,
            rx_eval_cd: r_x_cd,
            mrx_eval_cd: m_rx_cd,
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
