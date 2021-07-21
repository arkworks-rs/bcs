use crate::bcs::oracle::MessageFetchingOracle;
use crate::bcs::transcript::{LDTParameters, Transcript};
use crate::iop::prover::IOPProver;
use crate::iop::verifier::IOPVerifier;
use crate::iop::{EncodedProverMessage, MTHashParameters, MessageTree};
use crate::Error;
use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge};

/// TODO doc
pub struct BCSProof<MT, F, FinalHash>
where
    MT: MTConfig,
    F: PrimeField,
    MT::InnerDigest: Absorb,
    FinalHash: Clone,
{
    prover_message_oracle: MessageTree<MessageFetchingOracle<MT, F>>,
    final_hash: FinalHash,
}

impl<MT, F, FinalHash> BCSProof<MT, F, FinalHash>
where
    MT: MTConfig<Leaf = F>,
    F: PrimeField,
    MT::InnerDigest: Absorb,
    FinalHash: Clone,
{
    /// Generate proof
    pub fn generate<V, S, P>(
        sponge: S,
        prover_parameter: &P::ProverParameter,
        verifier_parameter: &P::VerifierParameter,
        hash_params: MTHashParameters<MT>,
        final_hasher: fn(&mut S) -> FinalHash,
    ) -> Result<Self, Error>
    where
        V: IOPVerifier<MT, S, F, VerifierParameter = P::VerifierParameter>,
        S: CryptographicSponge,
        P: IOPProver<MT, S, F>,
    {
        // create a BCS transcript
        let mut transcript = Transcript::new(sponge, hash_params);
        // run prover code
        transcript = P::prove(transcript, prover_parameter, verifier_parameter);
        // run LDT on message oracle
        {
            // TODO
        }
        // convert transcript to prover message oracle
        let mut recording_oracle = transcript
            .encoded_prover_messages
            .map_into(|x| x.into_oracle());
        let mut sponge = transcript.sponge;
        // run verifier code
        V::query_and_decision(
            &mut sponge,
            &mut recording_oracle,
            transcript.verifier_messages,
        )?;
        // convert oracle to message fetching oracle
        let fetching_oracle = recording_oracle.map_into(|x| x.into_message_fetching_oracle());
        // compute final hash
        let final_hash = final_hasher(&mut sponge);

        Ok(Self {
            prover_message_oracle: fetching_oracle,
            final_hash,
        })
    }

    /// Simulate FRI interaction with verifier
    fn generate_ldt_proof<S: CryptographicSponge>(
        ldt_parameters: &[(LDTParameters<F>, Vec<usize>)],
        encoded_prover_messages: &MessageTree<EncodedProverMessage<MT, F>>,
        sponge: &mut S,
    ) -> () {
        // iterate over ldt group
        for (ldt_param, ldt_group) in ldt_parameters.iter() {
            // sample random coefficient
            let rand_coeff: Vec<_> = sponge.squeeze_field_elements(ldt_group.len());
            // TODO: When LDT supports random combination, use that instead.
            // make a random combination
            let mut rand_comb: Vec<_> = (0..ldt_param.coset_domain.size())
                .map(|_| F::zero())
                .collect();
            for (coeff, &msg_index) in rand_coeff.iter().zip(ldt_group.iter()) {
                let oracle_msg = &encoded_prover_messages.direct[msg_index].leaves;
                rand_comb
                    .iter_mut()
                    .zip(oracle_msg.iter())
                    .for_each(|(comb, x)| *comb += *x * coeff);
            }
            // receive all queries
            let queries: Vec<usize> = (0..ldt_param.num_queries)
                .map(|_| le_bits_to_usize(&sponge.squeeze_bits(ldt_param.coset_domain.dim())))
                .collect();

            // TODO: subprotocol ldt
            todo!() // need to send all queried points
        }
    }
}

fn le_bits_to_usize(bits: &[bool]) -> usize {
    let mut result = 0;
    bits.iter().for_each(|&x| {
        result <<= 1;
        result |= x as usize;
    });
    result
}
