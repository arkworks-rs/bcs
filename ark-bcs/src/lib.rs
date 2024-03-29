#![cfg_attr(not(feature = "std"), no_std)]
#![doc = include_str!("../../README.md")]
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts, private_in_public, variant_size_differences)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_mut)]
#![deny(missing_docs)]
#![deny(unused_imports)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use)]
#![forbid(unsafe_code)]
#![recursion_limit = "256"]

#[macro_use]
extern crate derivative;

/// Defines some helper to debug user's IOP protocol.
#[macro_use]
pub mod tracer;

/// A public coin interactive oracle proof protocol.
/// Prover sends out messages that can be encoded to field elements. Verifier
/// sample messages using random oracle defined in `ark-sponge`.
pub mod iop;

/// A compiler to convert any public coin IOP to non-interactive one using BCS
/// transform. Source: [BCS16](https://eprint.iacr.org/2016/116)
pub mod bcs;
/// Low-degree test for RS-IOP. This implementation compiles LDT round function,
/// defined in `ark-ldt` to an IOP.
pub mod ldt;

/// Some handy imports for users.
pub mod prelude;
#[cfg(test)]
pub(crate) mod test_utils;

use ark_std::boxed::Box;

/// Universal Error Type
pub type Error = Box<dyn ark_std::error::Error>;
