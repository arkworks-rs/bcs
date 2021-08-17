use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};
use ark_bcs::iop::prover::IOPProver;
use ark_crypto_primitives::merkle_tree::Config;
use ark_bcs::bcs::transcript::{NameSpace, Transcript};
use ark_std::marker::PhantomData;
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::univariate::{DensePolynomial, DenseOrSparsePolynomial};
use ark_poly::{Radix2EvaluationDomain, UVPolynomial};
use ark_std::Zero;

pub struct SumcheckProver<F: PrimeField + Absorb>{
    _field: PhantomData<F>,
}

#[derive(Clone)]
pub struct SumcheckPublicInput<F: PrimeField + Absorb> {
    evaluation_domain: Radix2EvaluationDomain<F>,
    summation_domain: Radix2EvaluationDomain<F>,
    degree: usize,
    claimed_sum: F
}

#[derive(Clone)]
pub struct SumcheckPrivateInput<F: PrimeField + Absorb> {
    poly: DensePolynomial<F>
}

#[derive(Clone)]
pub struct SumcheckProverState<F: PrimeField + Absorb> {
    vp: SumcheckPublicInput<F>,
    wp: SumcheckPrivateInput<F>
}


impl<F: PrimeField + Absorb> IOPProver<F> for SumcheckProver<F> {
    type ProverParameter = ();
    type ProverState = SumcheckProverState<F>;
    type PublicInput = SumcheckPublicInput<F>;
    type PrivateInput = SumcheckPrivateInput<F>;

    fn initial_state(public_input: &Self::PublicInput, private_input: &Self::PrivateInput) -> Self::ProverState {
        SumcheckProverState{vp: public_input.clone(), wp: private_input.clone()}
    }

    fn prove<MT: Config<Leaf=[F]>, S: CryptographicSponge>(namespace: &NameSpace,
                                                           state: &mut Self::ProverState,
                                                           transcript: &mut Transcript<MT, S, F>,
                                                           prover_parameter: &Self::ProverParameter) -> Result<(), ark_bcs::Error> where MT::InnerDigest: Absorb {
        // from lecture
        let (hx, gx) = state.wp.poly.divide_by_vanishing_poly(state.vp.summation_domain.clone()).unwrap();
        let claim_sum_over_size
            = DensePolynomial::from_coefficients_vec(vec![state.vp.claimed_sum / F::from(state.vp.summation_domain.size as u128)]);
        let x = DensePolynomial::from_coefficients_vec(vec![F::zero(), F::one()]);
        let (px, r) = DenseOrSparsePolynomial::from(gx + (-claim_sum_over_size)).divide_with_q_and_r(&DenseOrSparsePolynomial::from(x)).unwrap();
        // remainder should be zero
        assert!(r.is_zero());
        let evaluation_domain_coset = Radix2CosetDomain::new(state.vp.evaluation_domain.clone(), F::one());

        let hx_degree_bound = state.vp.degree - state.vp.summation_domain.size as usize;
        let px_degree_bound = state.vp.summation_domain.size as usize - 1;

        transcript.send_univariate_polynomial(hx_degree_bound, &hx, evaluation_domain_coset)?;
        transcript.send_univariate_polynomial(px_degree_bound, &px, evaluation_domain_coset)?;

        transcript.submit_prover_current_round(namespace)?;
        Ok(())

    }
}


/// Univariate sumcheck (without LDT)
fn main() {
    todo!()
}