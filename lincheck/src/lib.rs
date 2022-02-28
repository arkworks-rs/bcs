#![cfg_attr(not(feature = "std"), no_std)]


pub mod matrix;

use ark_bcs::prelude::*;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_sponge::FieldElementSize::Full;
use ark_bcs::bcs::transcript::LDTInfo;
use ark_bcs::iop::message::OracleIndex;
use crate::matrix::{Matrix, MatrixSpec, NativeMatrixSpec};

/// Lincheck Protocol
/// We want to prove f_Mz = Mf_z where f_Mz and f_z is an RS code under codeword domain,
/// where f_Mz extends to `constraint_domain`, and f_z extends to `variable_domain`.
///
/// M is a matrix of shape `constraint_domain.size()` x `variable_domain.size()`.
pub struct Lincheck<F: PrimeField + Absorb> {
    pub constraint_domain: Radix2CosetDomain<F>,
    pub variable_domain: Radix2CosetDomain<F>,
}

impl<F: PrimeField + Absorb> Lincheck<F> {
    /// Send prover message to the transcript.
    /// `f_Mz`: an oracle handle of f_Mz
    /// `f_z`: f_z
    /// `mat`: Matrix where f_Mz = mat * f_z, using extension of both oracles
    pub fn prove<P: MTConfig<Leaf=[F]>, S: CryptographicSponge>(&self, transcript: &mut Transcript<P, S, F>, f_z: (MsgRoundRef, OracleIndex), mat: &Matrix<NativeMatrixSpec<F>>)
        where P::InnerDigest: Absorb
    {
        // receive alpha from verifier
        let alpha = transcript.squeeze_verifier_field_elements(&[Full])[0];

        // calculate `r(x)` of size `variable_domain.size()`, which is [1, alpha, alpha^2, ..., alpha^(variable_domain.size()-1)]
        let mut rx = Vec::with_capacity(self.variable_domain.size());
        rx.push(F::one());
        for _ in 1..self.variable_domain.size() {
            rx.push(*rx.last().unwrap() * alpha);
        }

        // LDE f_z to match the size of `variable_domain`
        let f_z_eval = transcript.get_previously_sent_prover_oracle(f_z.0, f_z.1);
        let f_z_coeff = transcript.codeword_domain().interpolate(f_z_eval.to_vec());
        let f_z_lde = self.variable_domain.evaluate(&f_z_coeff);

        todo!()


    }
}
