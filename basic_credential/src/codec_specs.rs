//! Round-trip lemmas of [`SignatureKeyPair`] (`tls_codec::spec::io`, the `std` path).
//!
//! `cfg(hax)`-only: empty lemma impls, whose contracts become proof obligations of the hax
//! extraction. `SignatureKeyPair` has no `SerializeBytes` impl, so only the `std` lemmas apply,
//! and derives `PartialEq` only under `cfg(hax)`, for these lemmas.

use tls_codec::spec::io::{NonEmptyStd, RoundTripStd};

use crate::SignatureKeyPair;

impl RoundTripStd for SignatureKeyPair {}
impl NonEmptyStd for SignatureKeyPair {}
