use crate::bcs::message::{ProverRoundMessageInfo, SuccinctRoundOracle, VerifierMessage};
use crate::tracer::TraceInfo;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{Namespace, SynthesisError};
use ark_std::borrow::Borrow;

/// Constraint Gadget for `RoundOracleVar`
pub trait RoundOracleVar<F: PrimeField> {}

#[derive(Clone)]
pub struct SuccinctRoundOracleVar<F: PrimeField> {
    /// Oracle Info
    pub info: ProverRoundMessageInfo,
    /// Leaves at query indices.
    pub queried_cosets: Vec<Vec<Vec<FpVar<F>>>>,
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
            coset_queries: Vec::new(),
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
        let queried_cosets = native
            .queried_cosets
            .iter()
            .map(|coset_for_all_oracles| {
                coset_for_all_oracles
                    .iter()
                    .map(|x| Vec::new_variable(cs.clone(), || Ok(x.clone()), mode))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        let short_messages = native
            .short_messages
            .iter()
            .map(|msg| {
                msg.iter()
                    .map(|x| FpVar::new_variable(cs.clone(), || Ok(*x), mode))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            info,
            queried_cosets,
            short_messages,
        })
    }
}

#[derive(Clone)]
pub struct SuccinctRoundOracleVarView<'a, F: PrimeField> {
    pub(crate) oracle: &'a SuccinctRoundOracleVar<F>,
    /// queries calculated by the verifier
    pub coset_queries: Vec<Vec<Boolean<F>>>,
    current_query_pos: usize,
}

impl<'a, F: PrimeField> SuccinctRoundOracleVarView<'a, F> {
    /// Return the leaves of at `position` of all oracle. `result[i][j]` is leaf `i` at oracle `j`.
    pub fn query(
        &mut self,
        position: &[Vec<Boolean<F>>],
        tracer: TraceInfo,
    ) -> Result<Vec<Vec<FpVar<F>>>, SynthesisError> {
        #[cfg(feature = "print-trace")]
        {
            println!(
                "[SimulationTranscript] Query {} leaves: {}",
                position.len(),
                tracer
            );
        }
        // convert the position to coset_index
        let log_coset_size = self.get_info().localization_parameter;
        let log_num_cosets = ark_std::log2(self.get_info().oracle_length) as usize - log_coset_size;
        let log_oracle_length = ark_std::log2(self.oracle.info.oracle_length) as usize;
        assert_eq!(log_oracle_length, log_coset_size + log_num_cosets);
        // coset index = position % num_cosets = the least significant `log_num_cosets` bits of pos
        // element index in coset = position / num_cosets = all other bits
        let coset_index = position
            .iter()
            .map(|pos| pos[..log_num_cosets].to_vec())
            .collect::<Vec<_>>();
        let element_index_in_coset = position
            .iter()
            .map(|pos| pos[log_num_cosets..log_oracle_length].to_vec())
            .collect::<Vec<_>>();
        let queried_coset = self.query_coset_without_tracer(&coset_index);
        queried_coset.into_iter()
            .zip(element_index_in_coset.into_iter())
            .map(|(coset_for_all_oracles, element_index)|{
                coset_for_all_oracles.into_iter()
                    // number of constraints here is O(Log(coset size))
                    .map(|coset|
                        // `conditionally_select_power_of_two_vector` need big endian position
                        FpVar::conditionally_select_power_of_two_vector(&element_index.clone().into_iter().rev().collect::<Vec<_>>(),
                                                                        &coset))
                    .collect::<Result<Vec<FpVar<_>>, _>>()
            }).collect::<Result<Vec<Vec<FpVar<_>>>, _>>()
    }

    /// Return the queried coset at `coset_index` of all oracles.
    /// `result[i][j][k]` is coset index `i` -> oracle index `j` -> element `k` in this coset.
    pub fn query_coset(
        &mut self,
        coset_index: &[Vec<Boolean<F>>],
        tracer: TraceInfo,
    ) -> Vec<Vec<Vec<FpVar<F>>>> {
        #[cfg(feature = "print-trace")]
        {
            println!(
                "[SuccinctRoundOracle] Query {} cosets: {}",
                coset_index.len(),
                tracer
            );
        };
        self.query_coset_without_tracer(coset_index)
    }

    fn query_coset_without_tracer(
        &mut self,
        coset_index: &[Vec<Boolean<F>>],
    ) -> Vec<Vec<Vec<FpVar<F>>>> {
        self.coset_queries.extend_from_slice(coset_index);
        assert!(
            self.current_query_pos + coset_index.len() <= self.oracle.queried_cosets.len(),
            "too many queries!"
        );
        let result = self.oracle.queried_cosets
            [self.current_query_pos..self.current_query_pos + coset_index.len()]
            .to_vec();
        self.current_query_pos += coset_index.len();
        result
    }

    /// Number of reed_solomon_codes oracles in this round.
    pub fn num_reed_solomon_codes_oracles(&self) -> usize {
        self.get_info().reed_solomon_code_degree_bound.len()
    }

    /// length of each oracle
    pub fn oracle_length(&self) -> usize {
        self.get_info().oracle_length
    }

    /// Get oracle info, including number of oracles for each type and degree bound of each RS code oracle.
    #[inline]
    pub fn get_info(&self) -> &ProverRoundMessageInfo {
        &self.oracle.info
    }

    /// Get degree bound of all reed-solomon codes in this round.
    pub fn get_degree_bound(&self) -> Vec<usize> {
        self.get_info().reed_solomon_code_degree_bound.clone()
    }

    /// Get non-oracle `i`th non-oracle short message in this round.
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
