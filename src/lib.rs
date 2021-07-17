//! A crate for interactive oracle proofs and BCS transform.
#![deny(unused_import_braces, unused_qualifications, trivial_casts)]
#![deny(trivial_numeric_casts, private_in_public, variant_size_differences)]
#![deny(stable_features, unreachable_pub, non_shorthand_field_patterns)]
#![deny(unused_attributes, unused_mut)]
#![deny(missing_docs)]
#![deny(unused_imports)]
#![deny(renamed_and_removed_lints, stable_features, unused_allocation)]
#![deny(unused_comparisons, bare_trait_objects, unused_must_use, const_err)]
#![forbid(unsafe_code)]

#[macro_use]
extern crate derivative;

use ark_std::fmt::Formatter;

/// A public coin, leaf handling, interactive oracle proof protocol.
pub mod iop;

/// A public coin interactive protocol where prover sends RS-code.
/// This module also includes a compiler to convert any RS-IOP to IOP.
pub mod rs_iop;

/// A compiler to convert any public coin IOP to non-interactive one using BCS transform.
/// Source: [BCS16](https://eprint.iacr.org/2016/116)
pub mod bcs;

/// Universal Error Type
pub type Error = Box<dyn ark_std::error::Error>;
#[derive(Debug)]
/// doc TODO
pub enum BCSError {
    /// doc TODO
    InvalidQuery,
}

impl ark_std::fmt::Display for BCSError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self {
            BCSError::InvalidQuery => write!(f, "Oracle does not contain answer to query."),
        }
    }
}

impl ark_std::error::Error for BCSError {}
