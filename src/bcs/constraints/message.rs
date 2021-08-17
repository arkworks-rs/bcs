use crate::bcs::message::{ProverRoundMessageInfo, SuccinctRoundOracle, VerifierMessage};
use crate::Error;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::borrow::Borrow;

/// Constraint Gadget for `RoundOracleVar`
pub trait RoundOracleVar<F: PrimeField> {
    /// Return the leaves of at `position` of all oracle. `result[i][j]` is leaf `i` at oracle `j`.
    fn query(&mut self, position: &[Vec<Boolean<F>>]) -> Result<Vec<Vec<FpVar<F>>>, Error>;

    /// Number of reed_solomon_codes oracles in this round.
    fn num_reed_solomon_codes_oracles(&self) -> usize {
        self.get_info().reed_solomon_code_degree_bound.len()
    }

    /// length of each oracle
    fn oracle_length(&self) -> usize {
        self.get_info().oracle_length
    }

    /// Get oracle info, including number of oracles for each type and degree bound of each RS code oracle.
    fn get_info(&self) -> ProverRoundMessageInfo;

    /// Get degree bound of all reed-solomon codes in this round.
    fn get_degree_bound(&self) -> Vec<usize> {
        self.get_info().reed_solomon_code_degree_bound
    }
}

#[derive(Clone)]
pub struct SuccinctRoundOracleVar<F: PrimeField> {
    /// Oracle Info
    pub info: ProverRoundMessageInfo,
    /// Leaves at query indices.
    pub queried_leaves: Vec<Vec<FpVar<F>>>,
    // note that queries will be provided by verifier instead
    /// Store the non-oracle IP messages in this round
    pub short_messages: Vec<Vec<FpVar<F>>>,
}

impl<F: PrimeField> SuccinctRoundOracleVar<F> {
    /// Return a view of succinct round oracle var. View contains a reference to the oracle,
    /// as well as recorded queries and position pointer.
    pub fn get_view(&self) -> SuccinctRoundOracleVarView<F> {
        SuccinctRoundOracleVarView {
            oracle: &self,
            queries: Vec::new(),
            current_query_pos: 0,
        }
    }
}

impl<F: PrimeField> AllocVar<SuccinctRoundOracle<F>, F> for SuccinctRoundOracleVar<F> {
    fn new_variable<T: Borrow<SuccinctRoundOracle<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into();
        let native = f()?;
        let native = native.borrow();
        let info = native.info.clone();
        let queried_leaves: Result<Vec<_>, _> = native
            .queried_leaves
            .iter()
            .map(|leaf| {
                let leaf_var: Result<Vec<_>, _> = leaf
                    .iter()
                    .map(|x| FpVar::new_variable(cs.clone(), || Ok(x.clone()), mode))
                    .collect();
                leaf_var
            })
            .collect();
        let queried_leaves = queried_leaves?;
        let short_messages: Result<Vec<_>, _> = native
            .short_messages
            .iter()
            .map(|msg| {
                let msg_var: Result<Vec<_>, _> = msg
                    .iter()
                    .map(|x| FpVar::new_variable(cs.clone(), || Ok(*x), mode))
                    .collect();
                msg_var
            })
            .collect();
        let short_messages = short_messages?;
        Ok(Self {
            info,
            queried_leaves,
            short_messages,
        })
    }
}

#[derive(Clone)]
pub struct SuccinctRoundOracleVarView<'a, F: PrimeField> {
    pub(crate) oracle: &'a SuccinctRoundOracleVar<F>,
    /// queries calculated by the verifier
    pub queries: Vec<Vec<Boolean<F>>>,
    current_query_pos: usize,
}

impl<'a, F: PrimeField> SuccinctRoundOracleVarView<'a, F> {
    pub fn query(
        &mut self,
        position: &[Vec<Boolean<F>>],
    ) -> Result<Vec<Vec<FpVar<F>>>, SynthesisError> {
        // TODO: record the position somewhere (instead of enforcing equality)
        self.queries.extend_from_slice(position);
        assert!(
            self.current_query_pos + position.len() <= self.oracle.queried_leaves.len(),
            "too many queries"
        );
        let result = self.oracle.queried_leaves
            [self.current_query_pos..self.current_query_pos + position.len()]
            .to_vec();
        Ok(result)
    }

    /// Return the leaves of at `position` of reed_solomon code oracle. `result[i][j]` is leaf `i` at oracle `j`.
    /// This method is convenient for LDT.
    /// Query position should be a coset, that has a starting index and stride.
    pub fn query_rs_code(
        &mut self,
        _starting_index: Vec<Boolean<F>>,
        _stride: u32,
    ) -> Result<Vec<Vec<FpVar<F>>>, Error> {
        todo!("implement this once LDT implementation is done.")
    }

    pub fn get_short_message(&self, index: usize) -> Vec<FpVar<F>> {
        self.oracle.short_messages[index].clone()
    }
}

#[derive(Clone)]
pub enum VerifierMessageVar<F: PrimeField> {
    /// Field elements
    FieldElements(Vec<FpVar<F>>),
    /// bits
    Bits(Vec<Boolean<F>>),
    /// bytes
    Bytes(Vec<UInt8<F>>),
}

impl<F: PrimeField> VerifierMessageVar<F> {
    pub fn try_into_field_elements(self) -> Option<Vec<FpVar<F>>> {
        if let VerifierMessageVar::FieldElements(fe) = self {
            Some(fe)
        } else {
            None
        }
    }

    pub fn try_into_bits(self) -> Option<Vec<Boolean<F>>> {
        if let VerifierMessageVar::Bits(bits) = self {
            Some(bits)
        } else {
            None
        }
    }

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
