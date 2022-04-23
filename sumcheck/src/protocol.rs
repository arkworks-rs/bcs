use crate::{
    vp::{DivVanishingPoly, VanishingPoly},
    UnivariateSumcheck,
};
use alloc::{vec, vec::Vec};
use ark_bcs::{
    bcs::transcript::{LDTInfo, Transcript},
    iop::{bookkeeper::NameSpace, message::OracleIndex, oracles::VirtualOracle},
    iop_trace,
    prelude::{MsgRoundRef, ProverRoundMessageInfo, SimulationTranscript},
};
use ark_crypto_primitives::merkle_tree::Config;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::{univariate::DensePolynomial, UVPolynomial};
use ark_sponge::{Absorb, CryptographicSponge};

#[derive(Debug, Clone, Copy)]
pub struct SumcheckPOracle<F: PrimeField> {
    pub summation_domain: Radix2CosetDomain<F>,

    pub claimed_sum: F,
    pub order_h_inv_times_claimed_sum: F,

    pub h_handle: (MsgRoundRef, OracleIndex),
    pub f_handle: (MsgRoundRef, OracleIndex),
}

impl<F: PrimeField> SumcheckPOracle<F> {
    pub fn new(
        summation_domain: Radix2CosetDomain<F>,
        claimed_sum: F,
        h_handle: (MsgRoundRef, OracleIndex),
        f_handle: (MsgRoundRef, OracleIndex),
    ) -> Self {
        let order_h_inv_times_claimed_sum =
            F::from(summation_domain.size() as u64).inverse().unwrap() * claimed_sum;
        Self {
            summation_domain,
            claimed_sum,
            order_h_inv_times_claimed_sum,
            h_handle,
            f_handle,
        }
    }
}

impl<F: PrimeField> VirtualOracle<F> for SumcheckPOracle<F> {
    fn constituent_oracle_handles(&self) -> Vec<(MsgRoundRef, Vec<OracleIndex>)> {
        vec![
            (self.h_handle.0, vec![self.h_handle.1]),
            (self.f_handle.0, vec![self.f_handle.1]),
        ]
    }

    fn evaluate(
        &self,
        coset_domain: Radix2CosetDomain<F>,
        constituent_oracles: &[Vec<F>],
    ) -> Vec<F> {
        let h_eval = &constituent_oracles[0];
        let f_eval = &constituent_oracles[1];
        let mut cur_x_inv = coset_domain.offset.inverse().unwrap();
        let z_h_eval =
            VanishingPoly::new(self.summation_domain).evaluation_over_coset(&coset_domain);
        let gen_inv = coset_domain.gen().inverse().unwrap();
        assert_eq!(h_eval.len(), f_eval.len());
        assert_eq!(h_eval.len(), z_h_eval.len());
        assert_eq!(h_eval.len(), coset_domain.size());
        f_eval
            .iter()
            .zip(h_eval)
            .zip(z_h_eval)
            .map(|((f, h), z_h)| {
                let result = (*f - self.order_h_inv_times_claimed_sum - z_h * *h) * cur_x_inv;
                cur_x_inv *= gen_inv;
                result
            })
            .collect::<Vec<_>>()
    }
}

impl<F: PrimeField + Absorb> UnivariateSumcheck<F> {
    /// Given a polynomial `f` to sum at domain `H`, return the actual sum, and
    /// polynomial `h` and `g` such that `p = h * Z_H + g * x + sum / |H|` where
    /// `Z_H` is the vanishing polynomial of `H`.
    ///
    /// # Returns
    /// * `h`: coefficient of polynomial `h` of degree `deg(f) - |H|`
    /// * `g`: coefficient of polynomial `g` of degree `|H| - 2`
    /// * `actual_sum`: actual sum of `f` over `H`
    pub fn calculate_h_g_and_actual_sum(
        &self,
        f: &DensePolynomial<F>,
    ) -> (DensePolynomial<F>, DensePolynomial<F>, F) {
        let vp = VanishingPoly::new(self.summation_domain);
        let (h, mut r) = f.divide_by_vp(vp);
        // we know r = x * g + sum / |H|. So g = (r - sum * |H|) / x
        let actual_sum = r.coeffs.remove(0) * F::from(self.summation_domain.size() as u64);
        let g = DensePolynomial::from_coefficients_vec(r.coeffs);
        (h, g, actual_sum)
    }

    pub fn degree_bound_of_g(&self) -> usize {
        self.summation_domain.size() - 1
    }

    /// Given a polynomial `f` to sum at domain `H`, return the actual sum, and
    /// polynomial `h` and `g` such that `p = h * Z_H + g * x + sum / |H|` where
    /// `Z_H` is the vanishing polynomial of `H`.
    ///
    /// # Returns
    /// * `h`: coefficient of polynomial `h`
    pub fn calculate_h(&self, f: &DensePolynomial<F>) -> DensePolynomial<F> {
        let vp = VanishingPoly::new(self.summation_domain);
        let (h, _) = f.divide_by_vp(vp);
        h
    }
    /// Send sumcheck message via transcript
    ///
    /// * `f`: coefficient of polynomial `f` to sum at domain `H`
    /// * `f_handlet`: where is `f` in transcript, represented as a round
    ///   reference and an oracle index in that round
    /// * `is_f_bounded`: whether `f` has degree bound
    /// # Panics
    /// Panics if there is a pending message not sent.
    pub fn prove<P: Config<Leaf = [F]>, S: CryptographicSponge>(
        &self,
        transcript: &mut Transcript<P, S, F>,
        ns: NameSpace,
        f_coeff: &DensePolynomial<F>,
        f_handle: (MsgRoundRef, OracleIndex),
        claimed_sum: F,
    ) where
        P::InnerDigest: Absorb,
    {
        let h = self.calculate_h(f_coeff);

        let h_eval = transcript.codeword_domain().evaluate(&h);
        let h_round = transcript
            .add_prover_round_with_codeword_domain()
            .send_oracle_message_without_degree_bound(h_eval)
            .submit(ns, iop_trace!("h oracle"))
            .unwrap();

        // register g as a virtual oracle
        let g_oracle = SumcheckPOracle::new(
            self.summation_domain,
            claimed_sum,
            (h_round, (0, false).into()),
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
    }

    /// Register sumcheck message via transcript
    pub fn register<P: Config<Leaf = [F]>, S: CryptographicSponge>(
        &self,
        transcript: &mut SimulationTranscript<P, S, F>,
        ns: NameSpace,
        f_handle: (MsgRoundRef, OracleIndex),
        claimed_sum: F,
    ) where
        P::InnerDigest: Absorb,
    {
        // receive h with no degree bound
        let round_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
            .with_num_message_oracles(1)
            .build();
        let h_handle =
            transcript.receive_prover_current_round(ns, round_info, iop_trace!("h oracle"));

        // register g as a virtual oracle
        let g_oracle = SumcheckPOracle::new(
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
    }

    // there is no need to do query phase. LDT will fail is sum is incorrect.
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::test_util::poseidon_parameters;
    use ark_bcs::{
        bcs::{prover::BCSProof, verifier::BCSVerifier, MTHashParameters},
        iop::{oracles::RoundOracle, prover::IOPProver, verifier::IOPVerifier, ProverParam},
        ldt::rl_ldt::{LinearCombinationLDT, LinearCombinationLDTParameters},
        prelude::MessagesCollection,
        Error,
    };
    use ark_bls12_381::Fr;
    use ark_crypto_primitives::{
        crh::poseidon,
        merkle_tree::{Config, IdentityDigestConverter},
    };
    use ark_ldt::domain::Radix2CosetDomain;
    use ark_poly::Polynomial;
    use ark_sponge::poseidon::PoseidonSponge;
    use ark_std::{test_rng, One};

    #[test]
    fn test_actual_sum() {
        let mut rng = test_rng();
        let summation_domain = Radix2CosetDomain::new_radix2_coset(64, Fr::from(123u64));
        let sumcheck = UnivariateSumcheck { summation_domain };
        let f = DensePolynomial::rand(100, &mut rng);
        let (_, _, actual_sum) = sumcheck.calculate_h_g_and_actual_sum(&f);
        let expected_sum = (0..summation_domain.size())
            .map(|i| f.evaluate(&summation_domain.element(i)))
            .sum::<Fr>();
        assert_eq!(actual_sum, expected_sum);
    }

    #[test]
    fn test_p_whole_oracle() {
        let mut rng = test_rng();
        let summation_domain = Radix2CosetDomain::new_radix2_coset(64, Fr::from(123u64));
        let f = DensePolynomial::rand(100, &mut rng);
        let sumcheck = UnivariateSumcheck { summation_domain };
        let (h, _, actual_sum) = sumcheck.calculate_h_g_and_actual_sum(&f);

        let codeword_domain = Radix2CosetDomain::new_radix2_coset(128, Fr::from(256u64));
        // let expected_g_eval_over_h = codeword_domain
        //     .evaluate(&g)
        //     .iter()
        //     .map(|x| *x * Fr::from(summation_domain.size() as
        // u64).inverse().unwrap()).collect::<Vec<_>>();

        let dummy_handle = (MsgRoundRef::default(), OracleIndex::default());

        let h_eval = codeword_domain.evaluate(&h);
        let f_eval = codeword_domain.evaluate(&f);
        let cons = [h_eval, f_eval];

        let g_oracle =
            SumcheckPOracle::new(summation_domain, actual_sum, dummy_handle, dummy_handle);
        let p = g_oracle.evaluate(codeword_domain, &cons);

        let p_coeff = codeword_domain.interpolate(p);
        assert_eq!(p_coeff.degree(), summation_domain.size() - 2);

        // if claimed sum is wrong, the degree of `g` will be large.
        let wrong_g_oracle = SumcheckPOracle::new(
            summation_domain,
            actual_sum + Fr::one(),
            dummy_handle,
            dummy_handle,
        );
        let p = wrong_g_oracle.evaluate(codeword_domain, &cons);

        let p_coeff = codeword_domain.interpolate(p);
        assert!(p_coeff.degree() > summation_domain.size() - 2);
    }

    pub(crate) const POLY_DEG: usize = 100;

    pub(crate) struct MockProtocol;

    #[derive(Clone, Debug)]
    pub(crate) struct MockProverParam {
        pub poly: DensePolynomial<Fr>,
        pub claimed_sum: Fr,
        pub summation_domain: Radix2CosetDomain<Fr>,
    }

    #[derive(Clone, Debug)]
    pub(crate) struct MockVerifierParam {
        pub summation_domain: Radix2CosetDomain<Fr>,
        pub claimed_sum: Fr,
    }

    impl ProverParam for MockProverParam {
        type VerifierParameter = MockVerifierParam;

        fn to_verifier_param(&self) -> Self::VerifierParameter {
            MockVerifierParam {
                summation_domain: self.summation_domain,
                claimed_sum: self.claimed_sum,
            }
        }
    }

    impl IOPProver<Fr> for MockProtocol {
        type ProverParameter = MockProverParam;
        type PublicInput = ();
        type PrivateInput = ();

        fn prove<MT: Config<Leaf = [Fr]>, S: CryptographicSponge>(
            namespace: NameSpace,
            _public_input: &Self::PublicInput,
            _private_input: &Self::PrivateInput,
            transcript: &mut Transcript<MT, S, Fr>,
            prover_parameter: &Self::ProverParameter,
        ) -> Result<(), Error>
        where
            MT::InnerDigest: Absorb,
        {
            let poly_handle = transcript
                .add_prover_round_with_codeword_domain()
                .send_univariate_polynomial(&prover_parameter.poly, POLY_DEG + 1)
                .submit(namespace, iop_trace!("poly to sum"))?;
            // just invoke sumcheck
            let sumcheck = UnivariateSumcheck {
                summation_domain: prover_parameter.summation_domain,
            };
            let sumcheck_ns = transcript.new_namespace(namespace, iop_trace!("sumcheck"));
            sumcheck.prove(
                transcript,
                sumcheck_ns,
                &prover_parameter.poly,
                (poly_handle, OracleIndex::new(0, true)),
                prover_parameter.claimed_sum,
            );
            Ok(())
        }
    }

    impl<S: CryptographicSponge> IOPVerifier<S, Fr> for MockProtocol {
        type VerifierOutput = ();
        type VerifierParameter = MockVerifierParam;
        type PublicInput = ();

        fn register_iop_structure<MT: Config<Leaf = [Fr]>>(
            namespace: NameSpace,
            transcript: &mut SimulationTranscript<MT, S, Fr>,
            verifier_parameter: &Self::VerifierParameter,
        ) where
            MT::InnerDigest: Absorb,
        {
            let poly_info = ProverRoundMessageInfo::new_using_codeword_domain(transcript)
                .with_reed_solomon_codes_degree_bounds(vec![POLY_DEG + 1])
                .build();
            let poly_handle = transcript.receive_prover_current_round(
                namespace,
                poly_info,
                iop_trace!("poly to sum"),
            );
            let sumcheck = UnivariateSumcheck {
                summation_domain: verifier_parameter.summation_domain,
            };
            let sumcheck_ns = transcript.new_namespace(namespace, iop_trace!("sumcheck"));
            sumcheck.register(
                transcript,
                sumcheck_ns,
                (poly_handle, OracleIndex::new(0, false)),
                verifier_parameter.claimed_sum,
            );
        }

        fn query_and_decide<O: RoundOracle<Fr>>(
            _namespace: NameSpace,
            _verifier_parameter: &Self::VerifierParameter,
            _public_input: &Self::PublicInput,
            _sponge: &mut S,
            _transcript_messages: &mut MessagesCollection<Fr, O>,
        ) -> Result<Self::VerifierOutput, Error> {
            // nothing to do here. LDT is everything.
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
    fn test_sumcheck_end_to_end() {
        // seems that LDT fails to verify multiple low-degree oracles. There may
        // be some problem in random linear coefficients etc.
        // update 4/16: LDT prove think there are 2 oracles, but LDT verify think there
        // are 3 oracles, causing mismatch in linear coefficients update 4/16:
        // bug fixed. TODO: fix same thing in constraints.

        let mut rng = test_rng();
        let sponge = PoseidonSponge::new(&poseidon_parameters());

        let codeword_domain = Radix2CosetDomain::new_radix2_coset(256, Fr::from(0x12345));
        let ldt_param = LinearCombinationLDTParameters::new(128, vec![1, 2, 1], codeword_domain, 5);
        let summation_domain = Radix2CosetDomain::new_radix2_coset(32, Fr::from(0x6789));

        let poly = DensePolynomial::rand(POLY_DEG, &mut rng);

        let claimed_sum = summation_domain.evaluate(&poly).into_iter().sum::<Fr>();

        let mt_hash_param = MTHashParameters::<FieldMTConfig> {
            leaf_hash_param: poseidon_parameters(),
            inner_hash_param: poseidon_parameters(),
        };

        let proof = BCSProof::generate::<MockProtocol, MockProtocol, LinearCombinationLDT<Fr>, _>(
            sponge.clone(),
            &(),
            &(),
            &MockProverParam {
                summation_domain,
                poly,
                claimed_sum,
            },
            &ldt_param,
            mt_hash_param.clone(),
        )
        .unwrap();

        // should not panic
        BCSVerifier::verify::<MockProtocol, LinearCombinationLDT<Fr>, _>(
            sponge,
            &proof,
            &(),
            &MockVerifierParam {
                summation_domain,
                claimed_sum,
            },
            &ldt_param,
            mt_hash_param,
        )
        .unwrap();
    }
}
