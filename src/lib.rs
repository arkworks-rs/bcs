//! A crate for interactive oracle proofs and BCS transform.
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts, private_in_public, variant_size_differences)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_mut)]
// #![deny(missing_docs)]
#![deny(unused_imports)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use, const_err)]
#![forbid(unsafe_code)]

#[macro_use]
extern crate derivative;

/// A public coin, leaf handling, interactive oracle proof protocol.
/// Prover sends out messages that can be encoded to field elements. Verifier sample field element as message.
pub mod iop;

/// A compiler to convert any public coin IOP to non-interactive one using BCS transform.
/// Source: [BCS16](https://eprint.iacr.org/2016/116)
pub mod bcs;
/// Defines trait for performing LDT.
/// TODO: move this to `ark-ldt`
pub mod ldt;

#[cfg(test)]
pub(crate) mod test_utils;

/// Universal Error Type
pub type Error = Box<dyn ark_std::error::Error>;
