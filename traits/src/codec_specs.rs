//! Round-trip lemmas of the wire types of [`crate::types`] (`tls_codec::spec`).
//!
//! `cfg(hax)`-only: empty lemma impls, whose contracts become proof obligations of the hax
//! extraction. Types without `PartialEq` in non-test builds (`HpkePrivateKey`) have none.

use tls_codec::spec::io::{NonEmptyStd, RoundTripStd};
use tls_codec::spec::{NonEmpty, RoundTrip};

use crate::types::{Ciphersuite, HpkeCiphertext, SignatureScheme, VerifiableCiphersuite};

// Byte-slice path: only `SignatureScheme` has a `SerializeBytes` impl.
impl RoundTrip for SignatureScheme {}
impl NonEmpty for SignatureScheme {}

// `std` path.
impl RoundTripStd for SignatureScheme {}
impl NonEmptyStd for SignatureScheme {}

impl RoundTripStd for HpkeCiphertext {}
impl NonEmptyStd for HpkeCiphertext {}

impl RoundTripStd for VerifiableCiphersuite {}
impl NonEmptyStd for VerifiableCiphersuite {}

impl RoundTripStd for Ciphersuite {}
impl NonEmptyStd for Ciphersuite {}
