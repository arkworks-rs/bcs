use ark_std::marker::PhantomData;

use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_sponge::{Absorb, CryptographicSponge};

use crate::{
    bcs::transcript::{SimulationTranscript, Transcript},
    iop::message::{RoundOracle, VerifierMessage},
    Error,
};
use ark_std::vec::Vec;

#[cfg(feature = "r1cs")]
/// R1CS constraints for LDT.
pub mod constraints;
/// LDT that runs FRI on a random linear combination.
pub mod rl_ldt;

/// Trait for LDT, which is an public coin IOP.
pub trait LDT<F: PrimeField + Absorb> {
    /// Parameters of `Self`
    type LDTParameters: Clone;

    /// Given the degree bound of codeword, return the expected evaluation
    /// domain and localization_parameter. localization parameter is
    /// log2(size of query coset) # Panics
    /// `ldt_info` will panic if `degree_bound` is not supported by this LDT.
    fn ldt_info(param: &Self::LDTParameters, degree_bound: usize) -> (Radix2CosetDomain<F>, usize);

    /// Given the list of codewords along with its degree bound, send LDT prover
    /// messages. `codewords[i][j][k]` is the `k`th leaf of `j`th RS oracle
    /// at IOP round `i`. LDT prover cannot send LDT oracles through
    /// `ldt_transcript`.
    fn prove<'a, MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        param: &Self::LDTParameters,
        codewords: impl IntoIterator<Item = &'a Vec<(Vec<F>, usize)>>,
        ldt_transcript: &mut Transcript<MT, S, F>,
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb;

    /// Simulate interaction with prover in commit phase, reconstruct verifier
    /// messages and verifier state using the sponge provided in the
    /// simulation transcript. Returns the verifier state for query and decision
    /// phase.
    fn register_iop_structure<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        param: &Self::LDTParameters,
        num_codewords_oracles: usize,
        transcript: &mut SimulationTranscript<MT, S, F>,
    ) where
        MT::InnerDigest: Absorb;

    /// Verify `codewords` is low-degree, given the succinct codewords oracle
    /// and proof. `codewords_oracles[i]` includes all oracles sent on round
    /// `i`.
    fn query_and_decide<S: CryptographicSponge, O: RoundOracle<F>>(
        param: &Self::LDTParameters,
        random_oracle: &mut S,
        codewords_oracles: Vec<&mut O>,
        ldt_prover_message_oracles: Vec<&mut O>,
        ldt_verifier_messages: &[Vec<VerifierMessage<F>>],
    ) -> Result<(), Error>;
}

/// A placeholder LDT, which does nothing.
pub struct NoLDT<F: PrimeField + Absorb> {
    _do_nothing: PhantomData<F>,
}

impl<F: PrimeField + Absorb> NoLDT<F> {
    /// Specify the evaluation domain and localization_parameter of the
    /// codeword, using this dummy LDT.
    pub fn parameter(
        evaluation_domain: Radix2CosetDomain<F>,
        localization_parameter: usize,
    ) -> (Radix2CosetDomain<F>, usize) {
        (evaluation_domain, localization_parameter)
    }
}

impl<F: PrimeField + Absorb> LDT<F> for NoLDT<F> {
    /// If LDTParameters is None, `ldt_info` will panic, so transcript would not
    /// allow low degree oracles to be sent.
    type LDTParameters = Option<(Radix2CosetDomain<F>, usize)>;

    fn ldt_info(
        param: &Self::LDTParameters,
        _degree_bound: usize,
    ) -> (Radix2CosetDomain<F>, usize) {
        param
            .as_ref()
            .expect("NoLDT has no evaluation domain configured")
            .clone()
    }

    fn prove<'a, MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        _param: &Self::LDTParameters,
        _codewords: impl IntoIterator<Item = &'a Vec<(Vec<F>, usize)>>,
        _ldt_transcript: &mut Transcript<MT, S, F>,
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb,
    {
        Ok(())
    }

    fn register_iop_structure<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        _param: &Self::LDTParameters,
        _num_codewords_oracles: usize,
        _transcript: &mut SimulationTranscript<MT, S, F>,
    ) where
        MT::InnerDigest: Absorb,
    {
        // do nothing
    }

    fn query_and_decide<S: CryptographicSponge, O: RoundOracle<F>>(
        _param: &Self::LDTParameters,
        _random_oracle: &mut S,
        _codewords_oracles: Vec<&mut O>,
        ldt_prover_message_oracles: Vec<&mut O>,
        ldt_verifier_messages: &[Vec<VerifierMessage<F>>],
    ) -> Result<(), Error> {
        assert!(
            ldt_prover_message_oracles.is_empty() && ldt_verifier_messages.is_empty(),
            "NoLDT should send no message"
        );
        // trivial: no query, no decide, always pass
        Ok(())
    }
}
