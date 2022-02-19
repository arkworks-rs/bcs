use crate::UnivariateSumcheck;
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
                let result = (f - self.order_h_inv_times_claimed_sum - &z_h * h) * &cur_x_inv;
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
        )
    }
}
