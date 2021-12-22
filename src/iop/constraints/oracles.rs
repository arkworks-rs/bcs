use std::borrow::Borrow;

use ark_ff::PrimeField;
use ark_ldt::domain::Radix2CosetDomain;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    fields::fp::FpVar,
    poly::domain::Radix2DomainVar,
    select::CondSelectGadget,
};
use ark_relations::r1cs::{Namespace, SynthesisError};

use crate::iop::{message::ProverRoundMessageInfo, oracles::SuccinctRoundMessage};

use super::message::MessagesCollectionVar;

#[derive(Clone)]
/// Round oracle variable that contains only queried leaves.
pub struct SuccinctRoundMessageVar<F: PrimeField> {
    /// Oracle Info
    pub info: ProverRoundMessageInfo,
    /// Leaves at query indices.
    pub queried_cosets: Vec<Vec<Vec<FpVar<F>>>>,
    // note that queries will be provided by verifier instead
    /// Store the non-oracle IP messages in this round
    pub short_messages: Vec<Vec<FpVar<F>>>,
}

impl<F: PrimeField> SuccinctRoundMessageVar<F> {
    /// Return a view of succinct round oracle var. View contains a reference to
    /// the oracle, as well as recorded queries and position pointer.
    pub fn get_view(&self) -> SuccinctRoundOracleVar<F> {
        SuccinctRoundOracleVar {
            oracle: &self,
            coset_queries: Vec::new(),
            current_query_pos: 0,
        }
    }
}

impl<F: PrimeField> AllocVar<SuccinctRoundMessage<F>, F> for SuccinctRoundMessageVar<F> {
    fn new_variable<T: Borrow<SuccinctRoundMessage<F>>>(
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
/// A reference to the succinct oracle variable plus a state recording current
/// query position.
pub struct SuccinctRoundOracleVar<'a, F: PrimeField> {
    pub(crate) oracle: &'a SuccinctRoundMessageVar<F>,
    /// queries calculated by the verifier
    pub coset_queries: Vec<Vec<Boolean<F>>>,
    current_query_pos: usize,
}

impl<'a, F: PrimeField> SuccinctRoundOracleVar<'a, F> {
    /// Return the leaves of at `position` of all oracle. `result[i][j]` is leaf
    /// `i` at oracle `j`.
    pub fn query(
        &mut self,
        position: &[Vec<Boolean<F>>],
    ) -> Result<Vec<Vec<FpVar<F>>>, SynthesisError> {
        // convert the position to coset_index
        let log_coset_size = self.get_info().localization_parameter;
        let log_num_cosets = ark_std::log2(self.get_info().oracle_length) as usize - log_coset_size;
        let log_oracle_length = ark_std::log2(self.oracle.info.oracle_length) as usize;
        assert_eq!(log_oracle_length, log_coset_size + log_num_cosets);
        // pad position to appropriate length
        let position = position
            .iter()
            .map(|bits| fit_bits_to_length(bits, log_oracle_length))
            .collect::<Vec<_>>();
        // coset index = position % num_cosets = the least significant `log_num_cosets`
        // bits of pos element index in coset = position / num_cosets = all
        // other bits
        let (coset_index, element_index_in_coset) =
            point_query_to_coset_query(&position, log_num_cosets);
        let queried_coset = self.query_coset_without_tracer(&coset_index);
        coset_query_response_to_point_query_response(queried_coset, element_index_in_coset)
    }

    /// Return the queried coset at `coset_index` of all oracles.
    /// `result[i][j][k]` is coset index `i` -> oracle index `j` -> element `k`
    /// in this coset.
    pub fn query_coset(&mut self, coset_index: &[Vec<Boolean<F>>]) -> Vec<Vec<Vec<FpVar<F>>>> {
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

    /// Get oracle info, including number of oracles for each type and degree
    /// bound of each RS code oracle.
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

fn point_query_to_coset_query<F: PrimeField>(
    point_indices: &[Vec<Boolean<F>>],
    log_num_cosets: usize,
) -> (Vec<Vec<Boolean<F>>>, Vec<Vec<Boolean<F>>>) {
    let coset_index = point_indices
        .iter()
        .map(|pos| pos[..log_num_cosets].to_vec())
        .collect::<Vec<_>>();
    let element_index_in_coset = point_indices
        .iter()
        .map(|pos| pos[log_num_cosets..].to_vec())
        .collect::<Vec<_>>();
    (coset_index, element_index_in_coset)
}

fn coset_query_response_to_point_query_response<F: PrimeField>(
    queried_coset: Vec<Vec<Vec<FpVar<F>>>>,
    element_index_in_coset: Vec<Vec<Boolean<F>>>,
) -> Result<Vec<Vec<FpVar<F>>>, SynthesisError> {
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

/// The constraints for coset evaluator defined by user, which takes a query
/// position (as index and coset) and use constituent oracles in iop messages to
/// build up responses.
pub type CosetVarEvaluator<CF> = Box<
    dyn Fn(
            &mut MessagesCollectionVar<CF>, // iop messages
            &[Vec<Boolean<CF>>],            // coset queries
            &[Radix2DomainVar<CF>],         // query cosets
        ) -> Result<Vec<Vec<Vec<FpVar<CF>>>>, SynthesisError>
        + 'static,
>;

/// A virtual oracle variable who make query to other virtual or non-virtual
/// oracles.
pub struct VirtualOracleVar<CF: PrimeField> {
    coset_evaluator: CosetVarEvaluator<CF>,
    pub(crate) codeword_domain: Radix2CosetDomain<CF>,
    pub(crate) localization_param: usize,
    pub(crate) test_bound: Vec<usize>,
    #[allow(unused)]
    pub(crate) constraint_bound: Vec<usize>,
}

impl<CF: PrimeField> VirtualOracleVar<CF> {
    /// Create a new virtual round given a coset evaluator. Note that one
    /// virtual round can have multiple virtual oracles.
    pub fn new(
        coset_evaluator: CosetVarEvaluator<CF>,
        codeword_domain: Radix2CosetDomain<CF>,
        localization_param: usize,
        test_bound: Vec<usize>,
        constraint_bound: Vec<usize>,
    ) -> Self {
        Self {
            coset_evaluator,
            codeword_domain,
            localization_param,
            test_bound,
            constraint_bound,
        }
    }

    /// Query the virtual oracle points at `positions` in the codeword domain.
    pub fn query_point(
        &self,
        positions: &[Vec<Boolean<CF>>],
        iop_messages: &mut MessagesCollectionVar<CF>,
    ) -> Result<Vec<Vec<FpVar<CF>>>, SynthesisError> {
        // convert the position to coset_index
        let log_coset_size = self.get_info().localization_parameter;
        let log_num_cosets = ark_std::log2(self.get_info().oracle_length) as usize - log_coset_size;

        let (coset_index, element_index_in_coset) =
            point_query_to_coset_query(positions, log_num_cosets);

        let queried_coset = self.query_coset(&coset_index, iop_messages)?;
        coset_query_response_to_point_query_response(queried_coset, element_index_in_coset)
    }

    /// Return the queried coset at `coset_index` of all oracles.
    /// `result[i][j][k]` is coset index `i` -> oracle index `j` -> element `k`
    /// in this coset.
    pub fn query_coset(
        &self,
        coset_index: &[Vec<Boolean<CF>>],
        iop_messages: &mut MessagesCollectionVar<CF>,
    ) -> Result<Vec<Vec<Vec<FpVar<CF>>>>, SynthesisError> {
        let codeword_domain_var = Radix2DomainVar::new(
            self.codeword_domain.gen(),
            self.codeword_domain.dim() as u64,
            FpVar::Constant(self.codeword_domain.offset),
        )?;

        // convert coset index to cosets
        let queried_cosets = coset_index
            .iter()
            .map(|idx| {
                Ok(codeword_domain_var
                    .query_position_to_coset(idx.as_slice(), self.localization_param as u64)?)
            })
            .collect::<Result<Vec<_>, _>>()?;

        (self.coset_evaluator)(iop_messages, coset_index, &queried_cosets)
    }

    /// Get oracle info, including number of oracles for each type and degree
    /// bound of each RS code oracle.
    pub fn get_info(&self) -> ProverRoundMessageInfo {
        ProverRoundMessageInfo::new(
            self.test_bound.clone(),
            0,
            0,
            self.codeword_domain.size(),
            self.localization_param,
        )
    }
}

/// fix a bit array to a certain length by remove extra element on the end or
/// pad with zero
fn fit_bits_to_length<F: PrimeField>(bits: &[Boolean<F>], length: usize) -> Vec<Boolean<F>> {
    if bits.len() < length {
        bits.to_vec()
            .into_iter()
            .chain((0..(length - bits.len())).map(|_| Boolean::FALSE))
            .collect()
    } else {
        (&bits[0..length]).to_vec()
    }
}
