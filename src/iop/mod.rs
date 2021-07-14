/// Public Coin IOP Prover
pub mod prover;
pub mod transcript;

use crate::Error;
use ark_crypto_primitives::merkle_tree::{Config as MTConfig, LeafParam, TwoToOneParam};
use ark_crypto_primitives::MerkleTree;
use ark_sponge::CryptographicSponge;
use ark_std::borrow::Borrow;
use ark_std::collections::BTreeMap;

/// Specify the merkle tree hash parameters used for this protocol.
#[derive(Clone)]
pub struct MTParameters<P: MTConfig> {
    /// Leaf hash parameter of merkle tree.
    pub leaf_hash_param: LeafParam<P>,
    /// Inner hash (TwoToOneHash) parameter of merkle tree.
    pub inner_hash_param: TwoToOneParam<P>,
}

/// Prover message for leaf-handling IOP prover.
/// TODO: For prover that wants to send polynomial, implement the trait `RSIOPProverMessage` instead.
pub trait IOPProverMessage<P: MTConfig> {
    /// A reference type to possibly unsized leaf.
    type Leaf: Borrow<P::Leaf>;
    /// list of `Leaf`
    type Leaves: IntoIterator<Item = Self::Leaf>;
    /// Encode the prover message to merkle tree leaves.
    /// Make sure to pad the leaf size fo power of 2.
    fn to_leaves(&self) -> Result<Self::Leaves, Error>;

    /// Encode the prover message to merkle tree.
    fn encode(
        &self,
        mt_param: &MTParameters<P>,
    ) -> Result<EncodedProverMessage<P, Self::Leaf>, Error> {
        let leaves: Vec<_> = self.to_leaves()?.into_iter().collect();
        let merkle_tree = MerkleTree::new(
            &mt_param.leaf_hash_param,
            &mt_param.inner_hash_param,
            leaves.iter().map(|x| x.borrow()),
        )?; // TODO: can we remove this clone here?
        Ok(EncodedProverMessage {
            leaves,
            merkle_tree,
        })
    }
}

/// Prover message encoded to a merkle tree.
pub struct EncodedProverMessage<P: MTConfig, L: Borrow<P::Leaf>> {
    /// Prover message encoded to leaves.
    pub leaves: Vec<L>,
    /// Merkle tree for leaves.
    pub merkle_tree: MerkleTree<P>,
}

/// Verifier message that is uniformly sampled from sponge.
pub trait IOPVerifierMessage<S: CryptographicSponge>: Clone {
    /// Sample the verifier message from sponge.
    fn from_sponge(sponge: &mut S) -> Self;
}

/// `SubprotocolMessage<T>` is the verifier message used by subprotocol, whose parent protocol
/// has verifier message `T`.
pub trait SubprotocolMessage<T: IOPVerifierMessage<S>, S: CryptographicSponge>:
    IOPVerifierMessage<S>
{
    fn into_parent_message(self) -> T;
    fn from_parent_message(parent_message: T) -> Self;
}

/// A tree-based data structure for storing protocol and subprotocol messages.
/// Can store either message or oracle, either prover message or verifier message.
pub struct MessageTree<T> {
    /// Non-subprotocol messages.
    pub direct: Vec<T>,
    /// subprotocol messages.
    /// Key is subprotocol id. Value is messages for subprotocols.
    /// Messages for different subprotocols may have different types, but they will
    /// are need to be wrapped by `T`.
    pub subprotocol: BTreeMap<usize, MessageTree<T>>,
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
    pub fn push_current_protocol_message(&mut self, message: T) {
        self.direct.push(message)
    }

    /// Add a message from subprotocol to history.
    pub fn receive_subprotocol_messages(
        &mut self,
        subprotocol_id: usize,
        messages: MessageTree<T>,
    ) {
        if self.subprotocol.contains_key(&subprotocol_id) {
            panic!("messages with same subprotocol id already received")
        }
        self.subprotocol.insert(subprotocol_id, messages);
    }
}
