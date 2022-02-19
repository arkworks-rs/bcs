use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

use crate::{
    bcs::simulation_transcript::SimulationTranscript,
    iop::{message::MessagesCollection, prover::IOPProver, ProverParam, VerifierParam},
    Error,
};
use ark_crypto_primitives::merkle_tree::Config as MTConfig;

use super::{bookkeeper::NameSpace, oracles::RoundOracle};

/// The verifier for public coin IOP has two phases.  This is intended to be
/// used as an endpoint protocol. Any subprotocol does not need to implement
/// this trait. Any implementation of this trait can be transformed to SNARG by
/// BCS.
/// * **Commit Phase**: Verifier send message that is uniformly sampled from a
///   random oracle. Verifier
/// will receive prover oracle, that can use used to query later. This protocol
/// relies on public coin assumption described in [BCS16, section 4.1](https://eprint.iacr.org/2016/116.pdf#subsection.4.1), that the verifier does not
/// main state and postpones any query to after the commit phase.
/// * **Query And Decision Phase**: Verifier sends query and receive answer from
///   message oracle.
pub trait IOPVerifier<S: CryptographicSponge, F: PrimeField + Absorb> {
    /// Verifier Output
    ///
    /// TODO: Consider if we need to make sure `success` state is in
    /// `VerifierOutput` by using a trait. If verification failed, set `success`
    /// to false instead of panicking or returning `Err` result.
    type VerifierOutput: Clone;
    /// Verifier Parameter. Verifier parameter can be accessed in
    /// `register_iop_structure`, and can affect transcript structure
    /// (e.g. number of rounds and degree bound).
    type VerifierParameter: VerifierParam;
    /// Public input. Public input cannot be accessed in
    /// `register_iop_structure`, and thus cannot affect transcript
    /// structure (e.g. number of rounds).
    type PublicInput: ?Sized;

    /// Simulate interaction with prover in commit phase, reconstruct verifier
    /// messages and verifier state using the sponge provided in the
    /// simulation transcript. Returns the verifier state for query and decision
    /// phase.
    ///
    /// When writing test, use `transcript.check_correctness` after calling this
    /// method to verify the correctness of this method.
    fn register_iop_structure<MT: MTConfig<Leaf = [F]>>(
        namespace: NameSpace,
        transcript: &mut SimulationTranscript<MT, S, F>,
        verifier_parameter: &Self::VerifierParameter,
    ) where
        MT::InnerDigest: Absorb;

    /// Query the oracle using the random oracle. Run the verifier code, and
    /// return verifier output that is valid if prover claim is true.
    /// Verifier will return an error if prover message is obviously false,
    /// or oracle cannot answer the query.
    fn query_and_decide<O: RoundOracle<F>>(
        namespace: NameSpace,
        verifier_parameter: &Self::VerifierParameter,
        public_input: &Self::PublicInput,
        sponge: &mut S,
        transcript_messages: &mut MessagesCollection<F, O>,
    ) -> Result<Self::VerifierOutput, Error>;
}

/// `IOPVerifierForProver` is an auto-implemented trait. User does not
/// need to derive this trait manually.
///
/// This trait is an extension for `IOPVerifier`, requiring that the verifier
/// state type and parameter type is consistent with what is expected from the
/// prover implementation.
///
/// Any IOPVerifier that satisfies this requirement
/// automatically implements this trait.
pub trait IOPVerifierForProver<S: CryptographicSponge, F: PrimeField + Absorb, P: IOPProver<F>>:
    IOPVerifier<S, F>
where
    Self: IOPVerifier<
        S,
        F,
        VerifierParameter = <P::ProverParameter as ProverParam>::VerifierParameter,
        PublicInput = P::PublicInput,
    >,
{
}
impl<S: CryptographicSponge, F: PrimeField + Absorb, P: IOPProver<F>, V>
    IOPVerifierForProver<S, F, P> for V
where
    V: IOPVerifier<
        S,
        F,
        VerifierParameter = <P::ProverParameter as ProverParam>::VerifierParameter,
        PublicInput = P::PublicInput,
    >,
{
}
