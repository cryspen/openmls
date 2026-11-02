//! Round-trip lemmas of [`SignatureKeyPair`] (`tls_codec::spec::io`, the `std` path).
//!
//! `cfg(hax)`-only: empty lemma impls, whose contracts become proof obligations of the hax
//! extraction. `SignatureKeyPair` has no `SerializeBytes` impl, so only the `std` lemmas apply,
//! and derives `PartialEq` only under `cfg(hax)`, for these lemmas. Its two decoders agree, so
//! its `std` encoding also round-trips through the byte-slice decoder.

use tls_codec::spec::io::{DecodersAgree, NonEmptyStd, RoundTripMixed, RoundTripStd};

use crate::SignatureKeyPair;

impl RoundTripStd for SignatureKeyPair {}
impl NonEmptyStd for SignatureKeyPair {}
impl DecodersAgree for SignatureKeyPair {}
impl RoundTripMixed for SignatureKeyPair {}
