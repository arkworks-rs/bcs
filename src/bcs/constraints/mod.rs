use ark_crypto_primitives::crh::TwoToOneCRHSchemeGadget;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_crypto_primitives::CRHSchemeGadget;
use ark_ff::PrimeField;

pub mod message;
pub mod proof;
pub mod transcript;
pub mod verifier;

pub struct MTHashParametersVar<CF: PrimeField, MT: Config, MTG: ConfigGadget<MT, CF>> {
    pub leaf_params: <<MTG as ConfigGadget<MT, CF>>::LeafHash as CRHSchemeGadget<
        <MT as Config>::LeafHash,
        CF,
    >>::ParametersVar,
    pub inner_params: <<MTG as ConfigGadget<MT, CF>>::TwoToOneHash as TwoToOneCRHSchemeGadget<
        <MT as Config>::TwoToOneHash,
        CF,
    >>::ParametersVar,
}
