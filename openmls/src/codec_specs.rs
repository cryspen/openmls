//! Round-trip lemmas of the OpenMLS wire types (`tls_codec::spec::io`, the `std` path).
//!
//! `cfg(hax)`-only: empty lemma impls, whose contracts become proof obligations of the hax
//! extraction. OpenMLS types have no `SerializeBytes` impl, so only the `std` lemmas apply.
//! Left out: types without `PartialEq` in non-test builds (`SignContent`, `EncryptContext`,
//! `ReuseGuard`), `Extension` and `Extensions<T>` (through the opaque `RatchetTreeExtension`;
//! `Extensions<T>` also rejects duplicate extension types when decoding), and
//! `LastResortExtension`'s `NonEmptyStd` (its encoding is empty).

use tls_codec::spec::io::{NonEmptyStd, RoundTripStd};

use crate::{
    ciphersuite::{
        hash_ref::HashReference,
        signature::{Signature, SignaturePublicKey},
    },
    credentials::{Credential, CredentialType},
    extensions::{
        ApplicationIdExtension, ExtensionType, ExternalPubExtension, ExternalSender,
        LastResortExtension, RequiredCapabilitiesExtension, UnknownExtension,
    },
    messages::proposals::ProposalType,
    versions::ProtocolVersion,
};

// `u16`-coded enums (serializers reject the non-canonical `Other` / `Unknown` / `Custom` values).
impl RoundTripStd for ProtocolVersion {}
impl NonEmptyStd for ProtocolVersion {}
impl RoundTripStd for CredentialType {}
impl NonEmptyStd for CredentialType {}
impl RoundTripStd for ExtensionType {}
impl NonEmptyStd for ExtensionType {}
impl RoundTripStd for ProposalType {}
impl NonEmptyStd for ProposalType {}

// Derived codecs.
impl RoundTripStd for HashReference {}
impl NonEmptyStd for HashReference {}
impl RoundTripStd for Signature {}
impl NonEmptyStd for Signature {}
impl RoundTripStd for SignaturePublicKey {}
impl NonEmptyStd for SignaturePublicKey {}
impl RoundTripStd for Credential {}
impl NonEmptyStd for Credential {}
impl RoundTripStd for ApplicationIdExtension {}
impl NonEmptyStd for ApplicationIdExtension {}
impl RoundTripStd for RequiredCapabilitiesExtension {}
impl NonEmptyStd for RequiredCapabilitiesExtension {}
impl RoundTripStd for ExternalPubExtension {}
impl NonEmptyStd for ExternalPubExtension {}
impl RoundTripStd for ExternalSender {}
impl NonEmptyStd for ExternalSender {}
impl RoundTripStd for UnknownExtension {}
impl NonEmptyStd for UnknownExtension {}
impl RoundTripStd for LastResortExtension {}
