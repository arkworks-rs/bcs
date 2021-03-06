use ark_std::marker::PhantomData;

use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_sponge::{Absorb, CryptographicSponge};

use crate::{
    bcs::{simulation_transcript::SimulationTranscript, transcript::Transcript},
    iop::{
        bookkeeper::NameSpace,
        message::{MessagesCollection, MsgRoundRef},
        oracles::RoundOracle,
    },
    Error,
};

#[cfg(feature = "r1cs")]
/// R1CS constraints for LDT.
pub mod constraints;
/// LDT that runs FRI on a random linear combination.
pub mod rl_ldt;

/// Trait for LDT, which is an public coin IOP.
pub trait LDT<F: PrimeField + Absorb> {
    /// Parameters of `Self`
    type LDTParameters: Clone;

    /// Return the codeword domain used by this LDT.
    fn codeword_domain(param: &Self::LDTParameters) -> Option<Radix2CosetDomain<F>>;

    /// Return the localization parameter (size of query coset) of codewords
    /// used by this LDT.
    fn localization_param(param: &Self::LDTParameters) -> Option<usize>;

    /// Given the list of message round references along with its degree bound,
    /// generate a low degree test proof all reed solomon codes in each
    /// reference.
    fn prove<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        namespace: NameSpace,
        param: &Self::LDTParameters,
        transcript: &mut Transcript<MT, S, F>,
        codewords: &[MsgRoundRef],
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb;

    /// Simulate interaction with prover in commit phase, reconstruct verifier
    /// messages and verifier state using the sponge provided in the
    /// simulation transcript. Returns the verifier state for query and decision
    /// phase.
    fn register_iop_structure<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        namespace: NameSpace,
        param: &Self::LDTParameters,
        num_rs_oracles: usize,
        transcript: &mut SimulationTranscript<MT, S, F>,
    ) where
        MT::InnerDigest: Absorb;

    /// Verify `codewords` is low-degree, given the succinct codewords oracle
    /// and proof.
    ///
    /// * `codewords`: All codewords references whose reed solomon codes are
    ///   going to be low degree tested. We can treat it as a specialized
    ///   version of `oracle_ref`.
    /// * `ldt_prover_message_oracles`: LDT Prover messages sent.
    fn query_and_decide<S: CryptographicSponge, O: RoundOracle<F>>(
        namespace: NameSpace,
        param: &Self::LDTParameters,
        sponge: &mut S,
        codewords: &[MsgRoundRef],
        transcript_messages: &mut MessagesCollection<F, O>,
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

    /// `prove` for NoLDT is no-op.
    fn prove<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        _namespace: NameSpace,
        _param: &Self::LDTParameters,
        _transcript: &mut Transcript<MT, S, F>,
        _codewords: &[MsgRoundRef],
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb,
    {
        Ok(())
    }

    fn register_iop_structure<MT: MTConfig<Leaf = [F]>, S: CryptographicSponge>(
        _namespace: NameSpace,
        _param: &Self::LDTParameters,
        _num_codewords_oracles: usize,
        _transcript: &mut SimulationTranscript<MT, S, F>,
    ) where
        MT::InnerDigest: Absorb,
    {
        // do nothing
    }

    fn query_and_decide<S: CryptographicSponge, O: RoundOracle<F>>(
        _namespace: NameSpace,
        _param: &Self::LDTParameters,
        _sponge: &mut S,
        codewords: &[MsgRoundRef],
        transcript_messages: &mut MessagesCollection<F, O>,
    ) -> Result<(), Error> {
        // nop, but we need to check that all codewords have no RS codes
        let no_rs_code = codewords.iter().all(|round| {
            transcript_messages
                .get_prover_round_info(*round)
                .num_reed_solomon_codes_oracles()
                == 0
        });
        assert!(
            no_rs_code,
            "NoLDT enforces that main protocol does not send any RS code."
        );
        Ok(())
    }

    fn codeword_domain(_param: &Self::LDTParameters) -> Option<Radix2CosetDomain<F>> {
        None
    }

    fn localization_param(_param: &Self::LDTParameters) -> Option<usize> {
        None
    }
}
