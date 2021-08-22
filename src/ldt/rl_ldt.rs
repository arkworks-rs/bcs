use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};
use ark_std::marker::PhantomData;
use crate::ldt::LDT;
use ark_ldt::domain::Radix2CosetDomain;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use crate::bcs::transcript::{Transcript, SimulationTranscript, ROOT_NAMESPACE};
use crate::Error;
use crate::bcs::message::{SuccinctRoundOracleView, RoundOracle, VerifierMessage};
use ark_ldt::fri::FRIParameters;
use ark_ldt::fri::prover::FRIProver;

/// Implementation of LDT using FRI protocol. When taking multiple oracles, this protocol takes a random linear combination.
/// This protocol has only one enforced bound.
pub struct LinearCombinationFRI<F: PrimeField + Absorb>{
    _field: PhantomData<F>,
}


impl<F: PrimeField + Absorb> LDT<F> for LinearCombinationFRI<F> {

    type LDTParameters = FRIParameters<F>;

    fn ldt_info(param: &Self::LDTParameters, _degree_bound: usize) -> (Radix2CosetDomain<F>, usize) {
        let codeword_localization = param.localization_parameters[0];
        let codeword_domain = param.domain;
        (codeword_domain, codeword_localization as usize)
    }

    fn prove<'a, MT: MTConfig<Leaf=[F]>, S: CryptographicSponge>(param: &Self::LDTParameters,
                                                                 codewords: impl IntoIterator<Item=&'a Vec<(Vec<F>, usize)>>,
                                                                 ldt_transcript: &mut Transcript<MT, S, F>)
        -> Result<(), Error> where MT::InnerDigest: Absorb {
        let namespace = &ROOT_NAMESPACE; // TODO: fix this
        // first, get random linear combination of the codewords
        let codewords = codewords.into_iter().collect::<Vec<_>>();
        // get number of coefficients needed
        let num_oracles: usize = codewords.iter().map(|round|round.len()).sum();
        let random_coefficients = ldt_transcript
            .squeeze_verifier_field_elements(&(0..num_oracles).map(|_|FieldElementSize::Full).collect::<Vec<_>>());

        let mut result_codewords = (0..param.domain.size()).map(|_|F::zero()).collect::<Vec<_>>();
        codewords.into_iter().map(|round: &'a Vec<(Vec<F>, usize)>|{
            round.iter().map(|(evaluation, degree_bound)|{
               assert!(*degree_bound <= param.tested_degree as usize, "degree bound larger than testing degree");
               evaluation
            })
        }).flatten().zip(random_coefficients.iter()).for_each(|(oracle, coeff)|{
            assert_eq!(oracle.len(), result_codewords.len());
            result_codewords.iter_mut().zip(oracle.iter()).for_each(|(r, a)|*r += *coeff * *a)
        });

        let mut current_domain = param.domain;
        let mut current_evaluations = result_codewords;

        param.localization_parameters.iter().try_for_each(|&localization_param|->Result<(), Error>{
            let alpha = ldt_transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full])[0];
            ldt_transcript.submit_verifier_current_round(namespace);
            let (next_domain, next_evaluations) = FRIProver::interactive_phase_single_round(
                current_domain,
                current_evaluations.clone(),
                localization_param,
                alpha
            );
            // prover send out this evaluation as message
            // each leaf will contain a coset
            ldt_transcript.send_message_oracle_with_localization(next_evaluations.clone(), localization_param as usize)?;
            ldt_transcript.submit_prover_current_round(namespace)?;

            current_domain = next_domain;
            current_evaluations = next_evaluations;
            Ok(())
        })?;

        Ok(())
    }

    #[allow(unused)] // in progress
    fn restore_from_commit_phase<MT: MTConfig<Leaf=[F]>, S: CryptographicSponge>(param: &Self::LDTParameters,
                                                                                 codewords_oracles: Vec<&mut SuccinctRoundOracleView<F>>,
                                                                                 transcript: &mut SimulationTranscript<MT, S, F>)
        where MT::InnerDigest: Absorb  {
        todo!()
    }

    #[allow(unused)] // in progress
    fn query_and_decide<S: CryptographicSponge, O: RoundOracle<F>>(param: &Self::LDTParameters,
                                                                   random_oracle: &mut S,
                                                                   codewords_oracles: Vec<&mut O>,
                                                                   ldt_prover_message_oracles: Vec<&mut O>,
                                                                   ldt_verifier_messages: &[Vec<VerifierMessage<F>>]) -> Result<(), Error> {
        todo!()
    }
}



