use ark_std::collections::BTreeMap;

use crate::{iop::message::MsgRoundRef, tracer::TraceInfo};

/// Namespace is a unique id of the protocol in a transcript.
/// `Namespace{id=0}` is always reserved for root namespace.
#[derive(Copy, Clone, Debug, Derivative)]
#[derivative(PartialEq, PartialOrd, Ord, Eq)]
pub struct NameSpace {
    /// The global id of current namespace in the transcript.
    pub id: u64,
    /// Trace for the current namespace
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Ord = "ignore")]
    pub trace: TraceInfo,
    /// The protocol id of the parent protocol in current transcript.
    /// if `self.id==0`, then this field should be 0.
    #[derivative(PartialEq = "ignore", PartialOrd = "ignore", Ord = "ignore")]
    pub parent_id: u64,
}

impl NameSpace {
    /// Root namespace
    pub const fn root(trace: TraceInfo) -> Self {
        Self {
            id: 0,
            trace,
            parent_id: 0,
        }
    }

    /// Returns a Namespace
    pub(crate) const fn new(id: u64, trace: TraceInfo, parent_id: u64) -> Self {
        Self {
            id,
            trace,
            parent_id,
        }
    }
}

#[derive(Clone)]
/// Stores the ownership relation of each message to its protocol.
/// All data is managed by `ark-bcs` and users do not need to create the
/// Bookkeeper by themselves.
/// 
/// **In almost all cases, users do not need to interact with this struct.**
pub struct MessageBookkeeper {
    /// Store the messages by namespace id
    pub(crate) messages_store: BTreeMap<u64, MessageIndices>,
    /// An adjacancy list the subspaces called for current namespace, in order.
    pub(crate) ns_map: BTreeMap<u64, Vec<u64>>,
    /// Store the namespace details (e.g. trace) by id
    pub(crate) ns_details: BTreeMap<u64, NameSpace>,
    next_namespace_index: u64,
}

impl MessageBookkeeper {
    pub(crate) fn new(trace: TraceInfo) -> Self {
        let mut result = Self {
            messages_store: BTreeMap::default(),
            ns_map: BTreeMap::default(),
            ns_details: BTreeMap::default(),
            next_namespace_index: 0,
        };
        // initialize root namespace
        result.messages_store.insert(0, Default::default());
        result.ns_map.insert(0, Default::default());
        result.ns_details.insert(0, NameSpace::new(0, trace, 0));
        result.next_namespace_index = 1;
        result
    }

    pub(crate) fn new_namespace(&mut self, trace: TraceInfo, parent_id: u64) -> NameSpace {
        let ns = NameSpace::new(self.next_namespace_index, trace, parent_id);
        // add new namespace details
        self.ns_details.insert(ns.id, ns);
        // initialize the messages store for new namespace
        self.messages_store.insert(
            ns.id,
            MessageIndices {
                prover_rounds: Vec::new(),
                verifier_messages: Vec::new(),
            },
        );
        // initialize subspace store for new namespace
        self.ns_map.insert(ns.id, Vec::new());
        // attach new namespace as subspace for parent namespace
        self.ns_map.get_mut(&parent_id).unwrap().push(ns.id);

        self.next_namespace_index += 1;
        ns
    }

    /// Return all prover message reference sent at this point, in order.
    pub(crate) fn dump_all_prover_messages_in_order(&self) -> Vec<MsgRoundRef> {
        self.messages_store
            .values()
            .map(|v| v.prover_rounds.iter())
            .flatten()
            .map(|v| *v)
            .collect()
    }

    /// Get the id the subspace that got created at the `index`th call to the
    /// `new_subspace`
    pub(crate) fn get_subspace_id(&self, namespace_id: u64, index: usize) -> u64 {
        *self
            .ns_map
            .get(&namespace_id)
            .expect("namespace does not exist")
            .get(index)
            .expect("index out of range")
    }

    /// Get the subspace that got created at the `index`th call to the
    /// `new_subspace`
    pub(crate) fn get_subspace(&self, namespace: NameSpace, index: usize) -> NameSpace {
        let subspace_id = self.get_subspace_id(namespace.id, index);
        *self
            .ns_details
            .get(&subspace_id)
            .expect(&ark_std::format!("Invalid Subspace ID: {}", subspace_id).clone())
    }

    pub(crate) fn attach_prover_round_to_namespace(
        &mut self,
        namespace: NameSpace,
        round_index: usize,
        is_virtual: bool,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        let namespace_node = self
            .messages_store
            .get_mut(&namespace.id)
            .expect("namespace not found");
        let oracle_ref = MsgRoundRef::new(round_index, trace, is_virtual);
        namespace_node.prover_rounds.push(oracle_ref);
        oracle_ref
    }

    pub(crate) fn attach_verifier_round_to_namespace(
        &mut self,
        namespace: NameSpace,
        round_index: usize,
        trace: TraceInfo,
    ) -> MsgRoundRef {
        let namespace_node = self
            .messages_store
            .get_mut(&namespace.id)
            .expect("namespace not found");
        let oracle_ref = MsgRoundRef::new(round_index, trace, false);
        namespace_node.verifier_messages.push(oracle_ref);
        oracle_ref
    }

    /// Return the message indices for current namespace.
    pub(crate) fn get_message_indices(&self, namespace: NameSpace) -> &MessageIndices {
        self.messages_store
            .get(&namespace.id)
            .expect("message indices not exist")
    }
}

/// contains indices of current protocol messages.
#[derive(Clone, Derivative)]
#[derivative(Debug)]
pub struct MessageIndices {
    /// Indices of prover message round oracles in this namespace.
    pub prover_rounds: Vec<MsgRoundRef>,
    /// Indices of verifier round oracles in this namespace.
    pub verifier_messages: Vec<MsgRoundRef>,
}

impl Default for MessageIndices {
    fn default() -> Self {
        Self {
            prover_rounds: Default::default(),
            verifier_messages: Default::default(),
        }
    }
}
