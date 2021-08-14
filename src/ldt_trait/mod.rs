#[cfg(feature="r1cs")]
pub mod constraints;

use crate::bcs::message::{RoundOracle, SuccinctRoundOracleView, VerifierMessage};
use crate::bcs::transcript::{SimulationTranscript, Transcript};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_sponge::{Absorb, CryptographicSponge};
use std::marker::PhantomData;

/// Trait for LDT, which is an interactive oracle proof system.
/// TODO: move this into `ark-ldt`
pub trait LDT<F: PrimeField + Absorb> {
    type LDTProof: Clone + CanonicalSerialize + CanonicalDeserialize;
    type LDTParameters;

    /// Given the degree bound, return the enforced bound and poly domain used.
    /// # Panics
    /// `ldt_info` will panic if `degree_bound` is not supported by this LDT.
    fn ldt_info(param: &Self::LDTParameters, degree_bound: usize) -> (usize, Radix2CosetDomain<F>);

    /// Given the list of codewords along with its degree bound, send LDT prover messages.
    /// `codewords[i][j][k]` is the `k`th leaf of `j`th RS oracle at IOP round `i`.
    ///
    /// **important**: when simulating verifier in LDT, make sure verifier can only access prover message
    /// though `oracle.query`.  
    fn prove<'a, MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        param: &Self::LDTParameters,
        codewords: impl IntoIterator<Item = &'a Vec<(Vec<F>, usize)>>,
        ldt_transcript: &mut Transcript<MT, S, F>,
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb;

    fn restore_from_commit_phase<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        param: &Self::LDTParameters,
        codewords_oracles: Vec<&mut SuccinctRoundOracleView<F>>, // FRI only gets degree bound information from this phase
        transcript: &mut SimulationTranscript<MT, S, F>,
    ) where
        MT::InnerDigest: Absorb;

    /// Verify `codewords` is low-degree, given the succinct codewords oracle and proof.
    /// `codewords_oracles[i]` includes all oracles sent on round `i`.
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

impl<F: PrimeField + Absorb> LDT<F> for NoLDT<F> {
    type LDTProof = ();
    type LDTParameters = ();

    fn ldt_info(
        _param: &Self::LDTParameters,
        _degree_bound: usize,
    ) -> (usize, Radix2CosetDomain<F>) {
        panic!("NoLDT is only a placeholder, and does nothing.")
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

    fn restore_from_commit_phase<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        _param: &Self::LDTParameters,
        _codewords_oracles: Vec<&mut SuccinctRoundOracleView<F>>,
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
