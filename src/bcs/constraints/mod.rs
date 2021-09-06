use ark_crypto_primitives::crh::TwoToOneCRHSchemeGadget;
use ark_crypto_primitives::CRHSchemeGadget;
use ark_crypto_primitives::merkle_tree::Config;
use ark_crypto_primitives::merkle_tree::constraints::ConfigGadget;
use ark_ff::PrimeField;

/// Defines BCS prover constraints and proof variable.
pub mod proof;
/// Defines BCS transcript gadget.
pub mod transcript;
/// Defines BCS proof verifier gadget.
pub mod verifier;

/// Hash parameters constraints for merkle tree.
pub struct MTHashParametersVar<CF: PrimeField, MT: Config, MTG: ConfigGadget<MT, CF>> {
    /// parameter for leaf hash function
    pub leaf_params: <<MTG as ConfigGadget<MT, CF>>::LeafHash as CRHSchemeGadget<
        <MT as Config>::LeafHash,
        CF,
    >>::ParametersVar,
    /// parameter for two-to-one hash function
    pub inner_params: <<MTG as ConfigGadget<MT, CF>>::TwoToOneHash as TwoToOneCRHSchemeGadget<
        <MT as Config>::TwoToOneHash,
        CF,
    >>::ParametersVar,
}
