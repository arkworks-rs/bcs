use ark_ff::{FpParameters, PrimeField};
use ark_sponge::poseidon::{find_poseidon_ark_and_mds, PoseidonParameters};
#[allow(unused)]
use ark_std::{str::FromStr, vec, One, Zero};

type F = ark_bls12_381::Fr;

pub(crate) fn poseidon_parameters() -> PoseidonParameters<ark_bls12_381::Fr> {
    let full_rounds = 8;
    let partial_rounds = 31;
    let alpha = 5;
    let rate = 2;

    let (ark, mds) = find_poseidon_ark_and_mds::<F>(
        <F as PrimeField>::Params::MODULUS_BITS as u64,
        rate,
        full_rounds,
        partial_rounds,
        0,
    );

    PoseidonParameters::new(
        full_rounds as usize,
        partial_rounds as usize,
        alpha,
        mds,
        ark,
        rate,
        1,
    )
}
