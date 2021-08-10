use crate::bcs::message::{ProverRoundMessageInfo, RoundOracle};
use crate::Error;
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;

/// Enables simple access to the "gadget" version `RoundOracle`
pub trait RoundOracleWithGadget<F: PrimeField>: RoundOracle<F> {
    type Var: RoundOracleVar<F, Self>;
}

/// Constraint Gadget for `RoundOracleVar`
pub trait RoundOracleVar<F: PrimeField, Oracle: RoundOracle<F>> {
    /// Return the leaves of at `position` of all oracle. `result[i][j]` is leaf `i` at oracle `j`.
    fn query(&mut self, position: &[UInt32<F>]) -> Result<Vec<Vec<FpVar<F>>>, Error>;

    /// Return the leaves of at `position` of reed_solomon code oracle. `result[i][j]` is leaf `i` at oracle `j`.
    /// This method is convenient for LDT.
    /// Query position should be a coset, that has a starting index and stride.
    /// Verifier must ensure `starting_index < stride`
    fn query_rs_code(
        &mut self,
        starting_index: UInt32<F>,
        stride: u32,
    ) -> Result<Vec<Vec<FpVar<F>>>, Error> {
        // This is naive implementation, where we use `self.query`.
        // TODO: use another merkle tree to store each coset together.
        let oracle_length = self.oracle_length() as u32;
        debug_assert!(
            oracle_length % stride == 0,
            "stride should be dividing oracle length!"
        );
        // generate position list
        let position: Result<Vec<_>, _> = (0..(oracle_length / stride))
            .map(|x| UInt32::addmany(&[starting_index, UInt32::constant(stride * x)]))
            .collect();
        let position = position?;
        let num_rs_codes = self.num_reed_solomon_codes_oracles();
        let query_responses = self.query(&position)?;
        let result: Vec<_> = query_responses
            .into_iter()
            .map(|mut resp| {
                resp.truncate(num_rs_codes);
                resp
            })
            .collect();
        Ok(result)
    }

    /// Number of reed_solomon_codes oracles in this round.
    fn num_reed_solomon_codes_oracles(&self) -> usize;

    /// length of each oracle
    fn oracle_length(&self) -> usize;

    /// Get oracle info, including number of oracles for each type and degree bound of each RS code oracle.
    fn get_info(&self) -> ProverRoundMessageInfo;

    /// Get degree bound of all reed-solomon codes in this round.
    fn get_degree_bound(&self) -> Vec<usize> {
        self.get_info().reed_solomon_code_degree_bound
    }
}
