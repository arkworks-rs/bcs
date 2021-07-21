use crate::iop::{EncodedProverMessage, MTHashParameters, MessageTree, SubprotocolID};

use ark_crypto_primitives::merkle_tree::Config as MTConfig;
use ark_ff::PrimeField;
use ark_sponge::{Absorb, CryptographicSponge, FieldElementSize};

use crate::Error;
use ark_crypto_primitives::MerkleTree;
use ark_ldt::domain::Radix2CosetDomain;
use ark_poly::univariate::DensePolynomial;
use ark_poly::Polynomial;

/// A communication protocol for IOP prover.
#[derive(Clone)]
pub struct Transcript<P: MTConfig, S: CryptographicSponge, F: PrimeField> {
    /// merkle tree hash parameters
    pub hash_params: MTHashParameters<P>,
    /// Message sent by prover in commit phase.
    pub encoded_prover_messages: MessageTree<EncodedProverMessage<P, F>>,
    /// Sampled Message sent by verifier in commit phase.
    pub verifier_messages: MessageTree<Vec<F>>,
    /// pair of ldt_parameters, and indices of current round prover messages verified by this ldt
    pub ldt_parameters: Vec<(LDTParameters<F>, Vec<usize>)>,
    /// Random Oracle to sample verifier messages.
    pub sponge: S,
}

/// Parent transcript where subprotocol is running.
pub struct TranscriptWithoutSponge<P: MTConfig, F: PrimeField> {
    encoded_prover_messages: MessageTree<EncodedProverMessage<P, F>>,
    verifier_messages: MessageTree<Vec<F>>,
    ldt_parameters: Vec<(LDTParameters<F>, Vec<usize>)>,
}

/// Parameters for LDT
#[derive(Clone)]
pub struct LDTParameters<F: PrimeField> {
    /// coset evaluation domain to convert polynomial to evaluation oracles
    pub coset_domain: Radix2CosetDomain<F>,
    /// degree bound of all polynomials using this LDT
    pub degree_bound: usize,
    /// FRI localization_parameters: At each round `i`, domain size will shrink to `last_round_domain_size` / `localization_parameters[i]`^2
    pub localization_parameters: Vec<u64>,
    /// number of queries to ensure soundness
    pub num_queries: usize,
}

/// In `Transcript::send_polynomial`, any polynomial with same LowDegreeTestHandle will
/// be made into a linear combination for LDT.
pub struct LowDegreeTestHandle {
    ldt_index: usize,
}

impl<P, S, F> Transcript<P, S, F>
where
    P: MTConfig<Leaf = F>,
    S: CryptographicSponge,
    F: PrimeField,
    P::InnerDigest: Absorb,
{
    /// Return a new BCS transcript.
    pub fn new(sponge: S, hash_params: MTHashParameters<P>) -> Self {
        Self {
            encoded_prover_messages: MessageTree::new(),
            verifier_messages: MessageTree::new(),
            sponge,
            hash_params,
            ldt_parameters: Vec::new(),
        }
    }

    /// Create a new LDT handle. Any univariate polynomial with the same handle will be linearly combined
    /// for low-degree test.
    pub fn create_ldt_handle(&mut self, ldt_parameters: LDTParameters<F>) -> LowDegreeTestHandle {
        // verify ldt parameter validity
        if ldt_parameters.coset_domain.size() < ldt_parameters.degree_bound + 1 {
            panic!("coset domain size is less than degree bound + 1")
        }
        self.ldt_parameters.push((ldt_parameters, Vec::new()));
        LowDegreeTestHandle {
            ldt_index: self.ldt_parameters.len() - 1,
        }
    }

    /// Send univariate polynomial with LDT.
    pub fn send_univariate_polynomial(
        &mut self,
        ldt_handle: &LowDegreeTestHandle,
        poly: &DensePolynomial<F>,
    ) -> Result<usize, Error> {
        let msg = {
            // get ldt information
            let (ldt_parameters, _) = self
                .ldt_parameters
                .get_mut(ldt_handle.ldt_index)
                .expect("invalid handle");
            // sanity check on size bound
            if poly.degree() > ldt_parameters.degree_bound {
                panic!("polynomial degree is greater than degree bound")
            }
            // convert poly to oracle evaluation
            ldt_parameters.coset_domain.evaluate(&poly)
        };

        // send message oracle
        let index = self.send_message_oracle(msg)?;
        // add message to ldt group
        self.ldt_parameters[ldt_handle.ldt_index].1.push(index);

        Ok(index)
    }

    /// Send prover message oracles.
    /// Note that transcript will not do low-degree test on this oracle.
    /// Returns the index of message.
    pub fn send_message_oracle(
        &mut self,
        msg: impl IntoIterator<Item = F>,
    ) -> Result<usize, Error> {
        // encode the message
        let encoded = self.encode_message_oracle(msg)?;
        // calculate the mt root
        let mt_root = encoded.merkle_tree.root();
        // absorb the mt root
        self.sponge.absorb(&mt_root);
        // store the encoded prover message for generating proof
        let index = self
            .encoded_prover_messages
            .push_current_protocol_message(encoded);

        Ok(index)
    }

    fn encode_message_oracle(
        &self,
        msg: impl IntoIterator<Item = F>,
    ) -> Result<EncodedProverMessage<P, F>, Error> {
        let leaves: Vec<_> = msg.into_iter().collect();
        let merkle_tree = MerkleTree::new(
            &self.hash_params.leaf_hash_param,
            &self.hash_params.inner_hash_param,
            &leaves,
        )?;
        Ok(EncodedProverMessage {
            leaves,
            merkle_tree,
        })
    }

    /// Squeeze sampled verifier message from transcript.
    pub fn squeeze_verifier_message(&mut self, field_size: &[FieldElementSize]) -> Vec<F> {
        let msg = self.sponge.squeeze_field_elements_with_sizes(field_size);
        // store the verifier message for later decision phase
        self.verifier_messages
            .push_current_protocol_message(msg.clone());
        msg
    }

    /// Create a branch of `self` as a transcript to be used for subprotocol.
    /// Returns the transcript for subprotocol, and current transcript without sponge.
    pub fn create_branch(self) -> (Self, TranscriptWithoutSponge<P, F>) {
        let sponge = self.sponge;
        let branched = TranscriptWithoutSponge {
            encoded_prover_messages: self.encoded_prover_messages,
            verifier_messages: self.verifier_messages,
            ldt_parameters: self.ldt_parameters,
        };
        (Self::new(sponge, self.hash_params), branched)
    }
}

impl<P: MTConfig, F: PrimeField> TranscriptWithoutSponge<P, F> {
    /// Merge the subprotocol transcript to current transcript to updating the sponge state
    pub fn merge_branch<S: CryptographicSponge>(
        mut self,
        branch: Transcript<P, S, F>,
        subprotocol_id: SubprotocolID,
    ) -> Transcript<P, S, F> {
        // store the subprotocol messages to current transcript
        self.verifier_messages
            .receive_subprotocol_messages(subprotocol_id, branch.verifier_messages);
        self.encoded_prover_messages
            .receive_subprotocol_messages(subprotocol_id, branch.encoded_prover_messages);
        Transcript {
            hash_params: branch.hash_params,
            encoded_prover_messages: self.encoded_prover_messages,
            verifier_messages: self.verifier_messages,
            sponge: branch.sponge,
            ldt_parameters: self.ldt_parameters,
        }
    }
}
