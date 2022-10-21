use ark_bls12_381::Fr;
use ark_ff::PrimeField;
use ark_sponge::poseidon::{find_poseidon_ark_and_mds, PoseidonConfig};

pub(crate) fn poseidon_parameters() -> PoseidonConfig<Fr> {
    let full_rounds = 8;
    let partial_rounds = 31;
    let alpha = 5;
    let rate = 2;

    let (ark, mds) = find_poseidon_ark_and_mds::<Fr>(
        Fr::MODULUS_BIT_SIZE as u64,
        rate,
        full_rounds,
        partial_rounds,
        0,
    );

    PoseidonConfig::new(
        full_rounds as usize,
        partial_rounds as usize,
        alpha,
        mds,
        ark,
        rate,
        1,
    )
}

#[cfg(feature = "r1cs")]
mod constraints {}
