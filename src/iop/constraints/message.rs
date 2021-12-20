use crate::{
    iop::{
        bookkeeper::{BookkeeperContainer, MessageBookkeeper, ToMsgRoundRef},
        message::{MsgRoundRef, ProverRoundMessageInfo, VerifierMessage},
    },
    tracer::TraceInfo,
};
use ark_ff::PrimeField;
use ark_r1cs_std::{fields::fp::FpVar, prelude::*};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{borrow::Borrow, vec::Vec};

use super::oracles::{SuccinctRoundOracleVar, VirtualOracleVar};

impl<F: PrimeField> R1CSVar<F> for VerifierMessageVar<F> {
    type Value = VerifierMessage<F>;

    fn cs(&self) -> ConstraintSystemRef<F> {
        match self {
            Self::Bits(v) => v[0].cs(),
            Self::Bytes(v) => v[0].cs(),
            Self::FieldElements(v) => v[0].cs(),
        }
    }

    fn value(&self) -> Result<Self::Value, SynthesisError> {
        match self {
            Self::Bits(v) => Ok(Self::Value::Bits(v.value()?)),
            Self::Bytes(v) => Ok(Self::Value::Bytes(v.value()?)),
            Self::FieldElements(v) => Ok(Self::Value::FieldElements(v.value()?)),
        }
    }
}

/// Stores sent prover and verifier messages variables in order.
/// Message can be accessed using namespace, or `MsgRoundRef`.
/// This struct is used by verifier to access prover message oracles and
/// verifier messages.
pub struct MessagesCollectionVar<'a, F: PrimeField> {
    pub(crate) real_oracles: Vec<SuccinctRoundOracleVar<'a, F>>,
    #[allow(unused)]
    pub(crate) virtual_oracles: Vec<Option<VirtualOracleVar<F>>>,
    pub(crate) verifier_messages: Vec<Vec<VerifierMessageVar<F>>>,
    pub(crate) bookkeeper: MessageBookkeeper,
}

impl<'a, F: PrimeField> BookkeeperContainer for MessagesCollectionVar<'a, F> {
    fn _bookkeeper(&self) -> &MessageBookkeeper {
        &self.bookkeeper
    }
}

impl<'a, F: PrimeField> MessagesCollectionVar<'a, F> {
    pub(crate) fn new(
        real_oracles: Vec<SuccinctRoundOracleVar<'a, F>>,
        virtual_oracles: Vec<Option<VirtualOracleVar<F>>>,
        verifier_messages: Vec<Vec<VerifierMessageVar<F>>>,
        bookkeeper: MessageBookkeeper,
    ) -> Self {
        Self {
            real_oracles,
            virtual_oracles,
            verifier_messages,
            bookkeeper,
        }
    }

    /// Get verifier message at at requested round.
    pub fn verifier_round(&self, at: impl ToMsgRoundRef) -> &Vec<VerifierMessageVar<F>> {
        let at = at.to_verifier_msg_round_ref(&self.bookkeeper);
        &self.verifier_messages[at.index]
    }

    /// Get prover message at at requested round.
    pub fn prover_round<'b>(&'b mut self, at: impl ToMsgRoundRef) -> AtProverRoundVar<'a, 'b, F> {
        let round = at.to_prover_msg_round_ref(&self.bookkeeper);
        AtProverRoundVar::<'a, 'b, F> { _self: self, round }
    }

    /// Take a virtual oracle and return a shadow `self` that can be used by
    /// virtual oracle. Current `self` will be temporarily unavailable when
    /// querying to prevent circular dependency.
    fn take_virtual_oracle(&mut self, round: MsgRoundRef) -> (VirtualOracleVar<F>, Self) {
        assert!(round.is_virtual);

        // move a virtual oracle, and make it temporarily available when querying to
        // prevent circular dependency
        let virtual_round = ark_std::mem::take(
            self.virtual_oracles
                .get_mut(round.index)
                .expect("round out of range"),
        )
        .expect("Virtual oracle contains circular query: For example, A -> B -> C -> A");

        // construct a shadow MessageCollection to query the virtual oracle.
        let shadow_self = Self {
            bookkeeper: self.bookkeeper.clone(),
            real_oracles: std::mem::take(&mut self.real_oracles),
            virtual_oracles: std::mem::take(&mut self.virtual_oracles),
            verifier_messages: std::mem::take(&mut self.verifier_messages),
        };

        (virtual_round, shadow_self)
    }

    fn restore_from_shadow_self(
        &mut self,
        shadow_self: Self,
        round: MsgRoundRef,
        vo: VirtualOracleVar<F>,
    ) {
        self.real_oracles = shadow_self.real_oracles;
        self.virtual_oracles = shadow_self.virtual_oracles;
        self.verifier_messages = shadow_self.verifier_messages;
        self.virtual_oracles[round.index] = Some(vo);
    }

    /// Get prover's short messages sent at this round. Short messages are not
    /// serialized in Merkle tree. Instead, those IP-style short messages are
    /// directly included in proof variable.
    pub fn get_prover_short_message(
        &mut self,
        at: impl ToMsgRoundRef,
        index: usize,
        _tracer: TraceInfo,
    ) -> Vec<FpVar<F>> {
        let at = at.to_prover_msg_round_ref(&self.bookkeeper);
        if at.is_virtual {
            unimplemented!("Virtual oracle does not have short message");
        } else {
            self.real_oracles[at.index].get_short_message(index)
        }
    }

    /// Get metadata of current prover round message.
    pub fn get_prover_round_info(&self, at: impl ToMsgRoundRef) -> ProverRoundMessageInfo {
        let at = at.to_prover_msg_round_ref(&self.bookkeeper);
        if at.is_virtual {
            self.virtual_oracles
                .get(at.index)
                .expect("round out of range")
                .as_ref()
                .expect("Virtual oracle contains circular query: For example, A -> B -> C -> A")
                .get_info()
        } else {
            self.real_oracles[at.index].get_info().clone()
        }
    }
}

/// A temporary struct to for querying/viewing prover round message.
pub struct AtProverRoundVar<'a, 'b, F: PrimeField> {
    pub(crate) _self: &'b mut MessagesCollectionVar<'a, F>,
    pub(crate) round: MsgRoundRef,
}

impl<'a, 'b, F: PrimeField> AtProverRoundVar<'a, 'b, F> {
    /// Query the prover message as an evaluation oracle at the requested round
    /// at a point.
    pub fn query_point(
        &mut self,
        positions: &[Vec<Boolean<F>>],
        _tracer: TraceInfo,
    ) -> Result<Vec<Vec<FpVar<F>>>, SynthesisError> {
        let round = self.round;
        let _self = &mut self._self;
        if !round.is_virtual {
            return _self.real_oracles[round.index].query(positions);
        }

        let (virtual_round, mut shadow_self) = _self.take_virtual_oracle(round);

        let query_result = virtual_round.query_point(positions, &mut shadow_self);

        // restore self
        _self.restore_from_shadow_self(shadow_self, round, virtual_round);

        // return the query result
        query_result
    }

    /// Return the queried coset at `coset_index` of all oracles in this round.
    /// `result[i][j][k]` is coset index `i` -> oracle index `j` -> element `k`
    /// in this coset.
    pub fn query_coset(
        &mut self,
        positions: &[Vec<Boolean<F>>],
        _tracer: TraceInfo,
    ) -> Result<Vec<Vec<Vec<FpVar<F>>>>, SynthesisError> {
        let round = self.round;
        let _self = &mut self._self;
        if !round.is_virtual {
            return Ok(_self.real_oracles[round.index].query_coset(positions));
        }

        let (virtual_round, mut shadow_self) = _self.take_virtual_oracle(round);

        let query_result = virtual_round.query_coset(positions, &mut shadow_self)?;

        _self.restore_from_shadow_self(shadow_self, round, virtual_round);

        Ok(query_result)
    }
    /// Get prover's short messages sent at this round. Short messages are not
    /// serialized in Merkle tree. Instead, those IP-style short messages are
    /// directly included in proof variable.
    pub fn short_message(&mut self, index: usize, _tracer: TraceInfo) -> Vec<FpVar<F>> {
        let at = self.round;
        if at.is_virtual {
            unimplemented!("Virtual oracle does not have short message");
        } else {
            self._self.real_oracles[at.index].get_short_message(index)
        }
    }
}

#[derive(Clone)]
/// Verifier message variable used in transcript gadget
pub enum VerifierMessageVar<F: PrimeField> {
    /// Field elements
    FieldElements(Vec<FpVar<F>>),
    /// bits
    Bits(Vec<Boolean<F>>),
    /// bytes
    Bytes(Vec<UInt8<F>>),
}

impl<F: PrimeField> VerifierMessageVar<F> {
    /// If `self` contains field elements, return those elements. Otherwise
    /// return `None`.
    pub fn try_into_field_elements(self) -> Option<Vec<FpVar<F>>> {
        if let VerifierMessageVar::FieldElements(fe) = self {
            Some(fe)
        } else {
            None
        }
    }

    /// If `self` contains bits, return those bits. Otherwise return `None`.
    pub fn try_into_bits(self) -> Option<Vec<Boolean<F>>> {
        if let VerifierMessageVar::Bits(bits) = self {
            Some(bits)
        } else {
            None
        }
    }

    /// If `self` contains bytes, return those bytes. Otherwise return `None`.
    pub fn try_into_bytes(self) -> Option<Vec<UInt8<F>>> {
        if let VerifierMessageVar::Bytes(bytes) = self {
            Some(bytes)
        } else {
            None
        }
    }
}

impl<F: PrimeField> AllocVar<VerifierMessage<F>, F> for VerifierMessageVar<F> {
    fn new_variable<T: Borrow<VerifierMessage<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into();
        let msg = f()?;
        let msg = msg.borrow();
        match msg {
            VerifierMessage::FieldElements(elements) => {
                let var: Result<Vec<_>, _> = elements
                    .iter()
                    .map(|x| FpVar::new_variable(cs.clone(), || Ok(*x), mode))
                    .collect();
                Ok(VerifierMessageVar::FieldElements(var?))
            }
            VerifierMessage::Bits(bits) => {
                let var: Result<Vec<_>, _> = bits
                    .iter()
                    .map(|x| Boolean::new_variable(cs.clone(), || Ok(*x), mode))
                    .collect();
                Ok(VerifierMessageVar::Bits(var?))
            }
            VerifierMessage::Bytes(bytes) => {
                let var: Result<Vec<_>, _> = bytes
                    .iter()
                    .map(|x| UInt8::new_variable(cs.clone(), || Ok(*x), mode))
                    .collect();
                Ok(VerifierMessageVar::Bytes(var?))
            }
        }
    }
}
