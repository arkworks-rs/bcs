use crate::bcs::message::{MessageOracle, ProverMessagesInRound, VerifierMessage};
use crate::bcs::transcript::{SimulationTranscript, Transcript};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_sponge::{Absorb, CryptographicSponge};

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
    ///
    /// **important**: when simulating verifier in LDT, make sure verifier can only access prover message
    /// though `oracle.query`.  
    fn prove<MT: MTConfig, S: CryptographicSponge>(
        param: &Self::LDTParameters,
        codewords: &[(usize, &[F])],
        ldt_transcript: &mut Transcript<MT, S, F>,
    ) -> Result<(), Error>
    where
        MT::InnerDigest: Absorb;

    fn reconstruct_ldt_verifier_messages<MT: MTConfig, L: LDT<F>, S: CryptographicSponge, Oracle: MessageOracle<F>>(
        param: &Self::LDTParameters,
        codewords_oracles: &[(usize, &mut Oracle)], // FRI does not use codewords_oracles in commit phase though
        transcript: &mut SimulationTranscript<MT, S, F>,
    ) where
        MT::InnerDigest: Absorb; // TODO: need simulation transcript

    /// Verify `codewords` is low-degree, given the succinct codewords oracle and proof.
    fn query_and_decide<S: CryptographicSponge, Oracle: MessageOracle<F>>(
        param: &Self::LDTParameters,
        random_oracle: &mut S,
        codewords_oracles: &[(usize, &mut Oracle)],
        ldt_prover_message_oracles: &[&mut ProverMessagesInRound<F, Oracle>],
        ldt_verifier_messages: &[Vec<VerifierMessage<F>>],
    ) -> Result<(), Error>;
}
