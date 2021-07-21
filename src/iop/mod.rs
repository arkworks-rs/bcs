/// Public Coin IOP Prover
pub mod prover;
/// TODO doc
pub mod verifier;

use crate::bcs::oracle::MessageRecordingOracle;
use crate::Error;
use ark_crypto_primitives::merkle_tree::{Config as MTConfig, LeafParam, TwoToOneParam};
use ark_crypto_primitives::{MerkleTree, Path};
use ark_ff::PrimeField;
use ark_std::collections::BTreeMap;
use ark_std::iter::FromIterator;

/// Subprotocol ID
pub type SubprotocolID = usize;

/// Specify the merkle tree hash parameters used for this protocol.
#[derive(Clone)]
pub struct MTHashParameters<P: MTConfig> {
    /// Leaf hash parameter of merkle tree.
    pub leaf_hash_param: LeafParam<P>,
    /// Inner hash (TwoToOneHash) parameter of merkle tree.
    pub inner_hash_param: TwoToOneParam<P>,
}

/// Prover message for leaf-handling IOP prover.
pub trait IOPProverMessage<P: MTConfig<Leaf = F>, F: PrimeField>: Sized {
    /// list of `Leaf`
    type OracleMessages: IntoIterator<Item = F>;
    /// Encode the prover message to merkle tree leaves.
    /// Make sure to pad the leaf size fo power of 2.
    fn to_oracle_messages(&self) -> Result<Self::OracleMessages, Error>;

    /// Encode the prover message to merkle tree.
    fn encode(&self, mt_param: &MTHashParameters<P>) -> Result<EncodedProverMessage<P, F>, Error> {
        let leaves: Vec<_> = self.to_oracle_messages()?.into_iter().collect();
        let merkle_tree = MerkleTree::new(
            &mt_param.leaf_hash_param,
            &mt_param.inner_hash_param,
            leaves.clone(),
        )?;
        Ok(EncodedProverMessage {
            leaves,
            merkle_tree,
        })
    }
}

/// Prover oracle messages encoded to a merkle tree.
#[derive(Clone)]
pub struct EncodedProverMessage<P: MTConfig, F: PrimeField> {
    /// Prover message encoded to leaves.
    pub leaves: Vec<F>,
    /// Merkle tree for leaves.
    pub merkle_tree: MerkleTree<P>,
}

impl<P: MTConfig, F: PrimeField> EncodedProverMessage<P, F> {
    /// Convert `Self` to a oracle that can be queried.
    pub fn into_oracle(self) -> MessageRecordingOracle<P, F> {
        MessageRecordingOracle {
            encoded_message: self,
            query_responses: BTreeMap::new(),
        }
    }
}

/// An Oracle of encoded prover message.
/// IOP Verifier will use this oracle to query prover message.
pub trait ProverMessageOracle<P: MTConfig, F: PrimeField>: Sized {
    /// Query prover message at `position`. Returns answer and proof.
    ///
    /// `query` should return error if oracle cannot fetch value at that position.
    /// For example, in message oracle constructed from BCS proof, if query answer does not present
    /// in proof, this function will return an error.
    fn query(&mut self, position: &[usize]) -> Result<Vec<(F, Path<P>)>, Error>;

    /// Obtain the merkle tree root of the message.
    fn mt_root(&self) -> P::InnerDigest;
}

/// A tree-based data structure for storing protocol and subprotocol messages.
/// Can store either message or oracle, either prover message or verifier message.
#[derive(Derivative)]
#[derivative(Clone(bound = "T: Clone"))]
pub struct MessageTree<T> {
    /// Non-subprotocol messages.
    pub direct: Vec<T>,
    /// subprotocol messages.
    /// Key is subprotocol id. Value is messages for subprotocols.
    /// Messages for different subprotocols may have different types, but they will
    /// are need to be wrapped by `T`.
    pub subprotocol: BTreeMap<SubprotocolID, MessageTree<T>>,
}

impl<T> MessageTree<T> {
    /// returns an empty message history.
    pub fn new() -> Self {
        Self {
            direct: Vec::new(),
            subprotocol: BTreeMap::new(),
        }
    }

    /// Add a message from current protocol to history.
    /// Return the index of current message.
    pub fn push_current_protocol_message(&mut self, message: T) -> usize {
        self.direct.push(message);
        self.direct.len() - 1
    }

    /// Add a message from subprotocol to history.
    pub fn receive_subprotocol_messages(
        &mut self,
        subprotocol_id: SubprotocolID,
        messages: MessageTree<T>,
    ) {
        if self.subprotocol.contains_key(&subprotocol_id) {
            panic!("messages with same subprotocol id already received")
        }
        self.subprotocol.insert(subprotocol_id, messages);
    }

    /// Convert type of message.
    pub fn map_into<T2>(self, func: fn(T) -> T2) -> MessageTree<T2> {
        let direct: Vec<_> = self.direct.into_iter().map(|x| func(x)).collect();
        let subprotocol_msg_iter = self
            .subprotocol
            .into_iter()
            .map(|(i, v)| (i, v.map_into(func)));
        let subprotocol = BTreeMap::from_iter(subprotocol_msg_iter);
        MessageTree {
            direct,
            subprotocol,
        }
    }

    /// Convert type of message.
    pub fn map<T2>(&self, func: fn(&T) -> T2) -> MessageTree<T2> {
        let direct: Vec<_> = self.direct.iter().map(|x| func(x)).collect();
        let subprotocol_msg_iter = self.subprotocol.iter().map(|(&i, v)| (i, v.map(func)));
        let subprotocol = BTreeMap::from_iter(subprotocol_msg_iter);
        MessageTree {
            direct,
            subprotocol,
        }
    }
}
