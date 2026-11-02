//! Round-trip lemmas of the wire types of [`crate::types`] (`tls_codec::spec`).
//!
//! `cfg(hax)`-only: empty lemma impls, whose contracts become proof obligations of the hax
//! extraction. `HpkePrivateKey` derives `PartialEq` outside of `test-utils` builds only under
//! `cfg(hax)`, for these lemmas.

use tls_codec::spec::io::{NonEmptyStd, RoundTripStd};
use tls_codec::spec::{NonEmpty, RoundTrip};

use crate::types::{
    Ciphersuite, HpkeCiphertext, HpkePrivateKey, SignatureScheme, VerifiableCiphersuite,
};

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

impl RoundTripStd for HpkePrivateKey {}
impl NonEmptyStd for HpkePrivateKey {}
