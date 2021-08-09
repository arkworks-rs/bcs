use ark_ff::PrimeField;
use ark_std::marker::PhantomData;
use crate::iop::prover::IOPProver;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_sponge::{CryptographicSponge, Absorb, FieldElementSize};
use crate::bcs::transcript::{NameSpace, Transcript, SimulationTranscript, MessageBookkeeper};
use ark_std::test_rng;
use crate::iop::verifier::IOPVerifier;
use crate::bcs::message::{RoundOracle, VerifierMessage, ProverRoundMessageInfo};
use crate::Error;

/// Mock IOP prover that only sends message oracles and short messages.
pub(crate) struct MockTest1Prover<F: PrimeField + Absorb>{
    _field: PhantomData<F>
}

impl<F: PrimeField + Absorb> IOPProver<F> for MockTest1Prover<F> {
    type ProverParameter = ();
    type ProverState = ();
    type PublicInput = ();
    type PrivateInput = ();

    fn initial_state(_public_input: &Self::PublicInput, _private_input: &Self::PrivateInput) -> Self::ProverState {
        /*NO STATE NEEDED*/
    }

    fn prove<MT: MTConfig<Leaf=[F]>, S: CryptographicSponge>(namespace: &NameSpace, _state: &mut Self::ProverState, transcript: &mut Transcript<MT, S, F>, _prover_parameter: &Self::ProverParameter)
        where MT::InnerDigest: Absorb {
        let mut rng = test_rng();

        // prover send
        let msg1 = (0..4).map(|_|F::rand(&mut rng));
        transcript.send_message(msg1);
        let msg2 = (0..256).map(|_|F::rand(&mut rng));
        transcript.send_message_oracle(msg2).unwrap();
        let msg3 = (0..256).map(|_|F::rand(&mut rng));
        transcript.send_message_oracle(msg3).unwrap();
        transcript.submit_prover_current_round(namespace).unwrap();

        // verifier send
        let vm1 =  transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full, FieldElementSize::Full, FieldElementSize::Full]);
        let vm2 = transcript.squeeze_verifier_bytes(16);
        transcript.submit_verifier_current_round(namespace);

        // verifier send2
        transcript.squeeze_verifier_bits(19);
        transcript.submit_verifier_current_round(namespace);

        // prover send
        let msg3 = vm1.into_iter().map(|x|x.square());
        transcript.send_message(msg3);
        let msg4 = (0..256u128).map(|x|F::from(x) + F::from_le_bytes_mod_order(&vm2));
        transcript.send_message_oracle(msg4).unwrap();
        transcript.submit_prover_current_round(namespace).unwrap();

        // prover send 2
        let msg5 = (0..6).map(|_|F::rand(&mut rng));
        transcript.send_message(msg5);
        transcript.submit_prover_current_round(namespace).unwrap();
    }

}

pub(crate) struct MockTest1Verifier<F: PrimeField + Absorb>{
    _field: PhantomData<F>
}

impl<S: CryptographicSponge, F: PrimeField + Absorb> IOPVerifier<S, F> for MockTest1Verifier<F> {
    type VerifierOutput = ();
    type VerifierParameter = ();
    type VerifierState = ();
    type PublicInput = ();

    fn restore_state_from_commit_phase<MT: MTConfig<Leaf=[F]>>(namespace: &NameSpace, _public_input: &Self::PublicInput,
                                                     transcript: &mut SimulationTranscript<MT, S, F>, _verifier_parameter: &Self::VerifierParameter) where MT::InnerDigest: Absorb {
        // prover send
        let expected_info = ProverRoundMessageInfo{
            reed_solomon_code_degree_bound: vec![],
            num_message_oracles: 2,
            num_short_messages: 1,
            oracle_length: 256
        };
        transcript.receive_prover_current_round(namespace, &expected_info);

        // verifier send
        transcript.squeeze_verifier_field_elements(&[FieldElementSize::Full, FieldElementSize::Full, FieldElementSize::Full]);
        transcript.squeeze_verifier_field_bytes(16);
        transcript.submit_verifier_current_round(namespace);

        // verifier send2
        transcript.squeeze_verifier_field_bits(19);
        transcript.submit_verifier_current_round(namespace);

        // prover send
        let expected_info = ProverRoundMessageInfo{
            reed_solomon_code_degree_bound: vec![],
            num_message_oracles: 1,
            num_short_messages: 1,
            oracle_length: 256
        };
        transcript.receive_prover_current_round(namespace, &expected_info);

        // prover send2
        let expected_info = ProverRoundMessageInfo{
            reed_solomon_code_degree_bound: vec![],
            num_message_oracles: 0,
            num_short_messages: 1,
            oracle_length: 0
        };
        transcript.receive_prover_current_round(namespace, &expected_info);

    }

    fn initial_state_for_query_and_decision_phase(public_input: &Self::PublicInput) -> Self::VerifierState {
        /*none*/
    }

    fn query_and_decide<'a, O: 'a + RoundOracle<F>>(namespace: &NameSpace, verifier_parameter: &Self::VerifierParameter, verifier_state: &mut Self::VerifierState, random_oracle: &mut S, prover_message_oracle: impl IntoIterator<Item=&'a mut O>, verifier_messages: &[Vec<VerifierMessage<F>>], bookkeeper: &MessageBookkeeper) -> Result<Self::VerifierOutput, Error> {
        // TODO: add some verification on prover answer
        Ok(())
    }
}

