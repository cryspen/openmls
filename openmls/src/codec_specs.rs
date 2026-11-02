//! Round-trip lemmas of the OpenMLS wire types (`tls_codec::spec::io`, the `std` path).
//!
//! `cfg(hax)`-only: empty lemma impls, whose contracts become proof obligations of the hax
//! extraction. OpenMLS types have no `SerializeBytes` impl, so only the `std` lemmas apply.
//! `SignContent`, `EncryptContext` and `ReuseGuard` derive `PartialEq` outside of tests only under
//! `cfg(hax)`, for these lemmas. `Secret`'s round trip uses its constant-time `PartialEq`, whose
//! `equal_ct` is opaque in the extraction (assumed to compare the bytes).
//! Left out: `Extension` and `Extensions<T>` (through the opaque `RatchetTreeExtension`;
//! `Extensions<T>` also rejects duplicate extension types when decoding), and
//! `LastResortExtension`'s `NonEmptyStd` (its encoding is empty).
//!
//! `DecodersAgree` / `RoundTripMixed`: the `std` and byte-slice decoders agree, so the `std`
//! encoding also round-trips through the byte-slice decoder (as `MlsMessageIn` decodes). Left
//! out: `UnknownExtension` (no byte-slice decoder).

use tls_codec::spec::io::{DecodersAgree, NonEmptyStd, RoundTripMixed, RoundTripStd};

use crate::{
    ciphersuite::{
        hash_ref::HashReference,
        hpke::EncryptContext,
        signature::{SignContent, Signature, SignaturePublicKey},
        ReuseGuard, Secret,
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
impl RoundTripStd for SignContent {}
impl NonEmptyStd for SignContent {}
impl RoundTripStd for EncryptContext {}
impl NonEmptyStd for EncryptContext {}
impl RoundTripStd for ReuseGuard {}
impl NonEmptyStd for ReuseGuard {}
impl RoundTripStd for Secret {}
impl NonEmptyStd for Secret {}

// Agreement of the `std` and byte-slice decoders, and the round trip of the `std` encoding
// through the byte-slice decoder.
impl DecodersAgree for ProtocolVersion {}
impl RoundTripMixed for ProtocolVersion {}
impl DecodersAgree for CredentialType {}
impl RoundTripMixed for CredentialType {}
impl DecodersAgree for ExtensionType {}
impl RoundTripMixed for ExtensionType {}
impl DecodersAgree for ProposalType {}
impl RoundTripMixed for ProposalType {}
impl DecodersAgree for HashReference {}
impl RoundTripMixed for HashReference {}
impl DecodersAgree for Signature {}
impl RoundTripMixed for Signature {}
impl DecodersAgree for SignaturePublicKey {}
impl RoundTripMixed for SignaturePublicKey {}
impl DecodersAgree for Credential {}
impl RoundTripMixed for Credential {}
impl DecodersAgree for ApplicationIdExtension {}
impl RoundTripMixed for ApplicationIdExtension {}
impl DecodersAgree for RequiredCapabilitiesExtension {}
impl RoundTripMixed for RequiredCapabilitiesExtension {}
impl DecodersAgree for ExternalPubExtension {}
impl RoundTripMixed for ExternalPubExtension {}
impl DecodersAgree for ExternalSender {}
impl RoundTripMixed for ExternalSender {}
impl DecodersAgree for LastResortExtension {}
impl RoundTripMixed for LastResortExtension {}
impl DecodersAgree for SignContent {}
impl RoundTripMixed for SignContent {}
impl DecodersAgree for EncryptContext {}
impl RoundTripMixed for EncryptContext {}
impl DecodersAgree for ReuseGuard {}
impl RoundTripMixed for ReuseGuard {}
impl DecodersAgree for Secret {}
impl RoundTripMixed for Secret {}
