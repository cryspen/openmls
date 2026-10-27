/- The per-impl `Lawful` obligations of the tls_codec impls the derives emit on the wire types of
`openmls_traits::types`, statements exactly as generated in `Extraction/ProofObligations.lean`
(checked by `scripts/check_statements.py`). Each proof is one call of TlsCodec's derive tactics
(`Verification/Derive/Bytes.lean`, `Verification/Derive/Std.lean`,
`Verification/Derive/RoundTripStd.lean` for the round trip), or of the crate-specific lemmas of
`StdHelpers.lean`.

Obligations: all 48 of `Extraction/ProofObligations.lean`.
Axioms reached (`scripts/axiom_whitelist.txt`): ASSUMED `size_of`, `size_of_U16`, `size_of_U8`,
`numBits_eq_64` (`HpkeCiphertext`'s round trip); 1 signature-only stub (`core.io.error.Error.Insts.CoreFmtDebug.fmt`). -/
import TraitsCodec.Extraction
import TlsCodec.Verification.ProofObligations
import TlsCodec.Verification.Derive.Std
import TlsCodec.Verification.Derive.RoundTripStd
import TlsCodec.Verification.Derive.DecodersAgree
import TraitsCodec.Verification.StdHelpers
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace openmls_traits
open tls_codec tls_codec.Derive

theorem types.SignatureScheme.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecSize
  :=
  by derive_size_lawful [types.SignatureScheme.Insts.Tls_codecSize.tls_serialized_len] []

theorem types.SignatureScheme.Insts.Tls_codecSerializeBytes.Lawful :
  tls_codec.SerializeBytes.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecSerializeBytes
  :=
  by derive_ser_lawful types.SignatureScheme.Insts.Tls_codecSize.Lawful [types.SignatureScheme.Insts.Tls_codecSerializeBytes.tls_serialize_bytes, types.SignatureScheme.Insts.Tls_codecSize.tls_serialized_len, types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ECDSA_SECP256R1_SHA256, types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ECDSA_SECP384R1_SHA384, types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ECDSA_SECP521R1_SHA512, types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ED25519, types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ED448] [tls_codec.U16.Insts.Tls_codecSerializeBytes.Lawful]

theorem types.SignatureScheme.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful types.SignatureScheme.Insts.Tls_codecSize.Lawful [types.SignatureScheme.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, types.SignatureScheme.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.U16.Insts.Tls_codecDeserializeBytes.Lawful]

theorem types.HpkeCiphertext.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful types.HpkeCiphertext
  types.HpkeCiphertext.Insts.Tls_codecSize
  :=
  by derive_size_lawful [types.HpkeCiphertext.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]

theorem types.HpkeCiphertext.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful types.HpkeCiphertext
  types.HpkeCiphertext.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful types.HpkeCiphertext.Insts.Tls_codecSize.Lawful [types.HpkeCiphertext.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, types.HpkeCiphertext.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.Lawful]

theorem types.VerifiableCiphersuite.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful types.VerifiableCiphersuite
  types.VerifiableCiphersuite.Insts.Tls_codecSize
  :=
  by derive_size_lawful [types.VerifiableCiphersuite.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.U16.Insts.Tls_codecSize.Lawful]

theorem types.VerifiableCiphersuite.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful types.VerifiableCiphersuite
  types.VerifiableCiphersuite.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful types.VerifiableCiphersuite.Insts.Tls_codecSize.Lawful [types.VerifiableCiphersuite.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, types.VerifiableCiphersuite.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.U16.Insts.Tls_codecDeserializeBytes.Lawful]

theorem types.Ciphersuite.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful types.Ciphersuite
  types.Ciphersuite.Insts.Tls_codecSize
  :=
  by derive_size_lawful [types.Ciphersuite.Insts.Tls_codecSize.tls_serialized_len] []

theorem types.Ciphersuite.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful types.Ciphersuite
  types.Ciphersuite.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful types.Ciphersuite.Insts.Tls_codecSize.Lawful [types.Ciphersuite.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, types.Ciphersuite.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.U16.Insts.Tls_codecDeserializeBytes.Lawful]

theorem types.SignatureScheme.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecSerialize
  :=
  ser_lawful_of_some _ types.SignatureScheme.Insts.Tls_codecSize.Lawful SS.ser (fun _ => rfl)

theorem types.SignatureScheme.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecDeserialize
  :=
  de_lawful_of_runs _ types.SignatureScheme.Insts.Tls_codecSize.Lawful SS.de_runs (fun _ _ => rfl)

theorem types.HpkeCiphertext.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful types.HpkeCiphertext
  types.HpkeCiphertext.Insts.Tls_codecSerialize
  :=
  by derive_ser_std_lawful types.HpkeCiphertext.Insts.Tls_codecSize.Lawful
    [types.HpkeCiphertext.Insts.Tls_codecSerialize.tls_serialize, Shared0HpkeCiphertext.Insts.Tls_codecSize.tls_serialized_len]
    [types.HpkeCiphertext.Insts.Tls_codecSize, types.HpkeCiphertext.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful]

theorem types.HpkeCiphertext.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful types.HpkeCiphertext
  types.HpkeCiphertext.Insts.Tls_codecDeserialize
  :=
  by derive_de_std_lawful types.HpkeCiphertext.Insts.Tls_codecSize.Lawful
    [types.HpkeCiphertext.Insts.Tls_codecDeserialize.tls_deserialize]
    [types.HpkeCiphertext.Insts.Tls_codecSize, types.HpkeCiphertext.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful]

theorem types.HpkePrivateKey.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful types.HpkePrivateKey
  types.HpkePrivateKey.Insts.Tls_codecSize
  :=
  by derive_size_lawful [types.HpkePrivateKey.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSize.Lawful]

theorem types.HpkePrivateKey.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful types.HpkePrivateKey
  types.HpkePrivateKey.Insts.Tls_codecSerialize
  :=
  ser_lawful_of_runs _ types.HpkePrivateKey.Insts.Tls_codecSize.Lawful
    (encOut quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSerialize) (fun x => by
      have hs := size_ok quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSize.Lawful x
      exact ⟨_, HPK.size x _ hs, fun hle => Serialize.Lawful.enc_len
        quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSerialize.Lawful x _ hs hle,
        HPK.ser_runs x _ hs⟩)
    (fun _ => rfl)

theorem types.HpkePrivateKey.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful types.HpkePrivateKey
  types.HpkePrivateKey.Insts.Tls_codecDeserialize
  :=
  de_lawful_of_runs _ types.HpkePrivateKey.Insts.Tls_codecSize.Lawful HPK.de_runs (fun _ _ => rfl)

theorem types.HpkePrivateKey.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful types.HpkePrivateKey
  types.HpkePrivateKey.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful types.HpkePrivateKey.Insts.Tls_codecSize.Lawful [types.HpkePrivateKey.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, types.HpkePrivateKey.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecDeserializeBytes.Lawful]

theorem types.VerifiableCiphersuite.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful types.VerifiableCiphersuite
  types.VerifiableCiphersuite.Insts.Tls_codecSerialize
  :=
  ser_lawful_of_some _ types.VerifiableCiphersuite.Insts.Tls_codecSize.Lawful
    (fun x => ⟨2#usize, _, VC.size x, by have := imax_ge; simp; omega, by simp, VC.ser_runs x⟩)
    (fun _ => rfl)

theorem types.VerifiableCiphersuite.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful types.VerifiableCiphersuite
  types.VerifiableCiphersuite.Insts.Tls_codecDeserialize
  :=
  de_lawful_of_runs _ types.VerifiableCiphersuite.Insts.Tls_codecSize.Lawful VC.de_runs (fun _ _ => rfl)

theorem types.Ciphersuite.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful types.Ciphersuite
  types.Ciphersuite.Insts.Tls_codecDeserialize
  :=
  de_lawful_of_runs _ types.Ciphersuite.Insts.Tls_codecSize.Lawful CS.de_runs (fun _ _ => rfl)

theorem types.Ciphersuite.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful types.Ciphersuite
  types.Ciphersuite.Insts.Tls_codecSerialize
  :=
  ser_lawful_of_some _ types.Ciphersuite.Insts.Tls_codecSize.Lawful CS.ser (fun _ => rfl)


/-! ## Round trip (`src/codec_specs.rs`)

Byte-slice path of `SignatureScheme` (`RoundTrip`, `NonEmpty`): TlsCodec's derive tactics
(`Derive/Bytes.lean`). `std` path (`RoundTripStd`, `NonEmptyStd`): an `RtStd` fact per type
(TlsCodec's `Derive/RoundTripStd.lean`, `derive_rt_std`), from which the lemma traits follow.
`HpkeCiphertext`'s bound (two `VLBytes`) uses the ASSUMED `numBits_eq_64` (`imax_64`).
`HpkePrivateKey` (`PartialEq` derived under `cfg(hax)` only): its `SecretVLBytes` field through
`SecretVLBytes.rtStd` (`StdHelpers.lean`). -/

private theorem HC.rtStd : RtStd types.HpkeCiphertext.Insts.Tls_codecSerialize
    types.HpkeCiphertext.Insts.Tls_codecDeserialize (1 + 1) (2 ^ 30 + 3 + (2 ^ 30 + 3)) := by
  derive_rt_std (by have := imax_64; omega) types.HpkeCiphertext.Insts.Tls_codecSize.Lawful
    [types.HpkeCiphertext.Insts.Tls_codecSerialize.tls_serialize, Shared0HpkeCiphertext.Insts.Tls_codecSize.tls_serialized_len]
    [types.HpkeCiphertext.Insts.Tls_codecSize, types.HpkeCiphertext.Insts.Tls_codecSize.tls_serialized_len]
    [types.HpkeCiphertext.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]
    [VLBytes.rtStd, VLBytes.rtStd]

theorem types.HpkeCiphertext.Insts.CoreCmpPartialEqHpkeCiphertext.Lawful :
  core.cmp.PartialEq.Lawful types.HpkeCiphertext types.HpkeCiphertext
  types.HpkeCiphertext.Insts.CoreCmpPartialEqHpkeCiphertext
  := by
  derive_eq_lawful [types.HpkeCiphertext.Insts.CoreCmpPartialEqHpkeCiphertext.eq] [VLBytes.partialEq_lawful, VLBytes.partialEq_lawful]

theorem types.HpkeCiphertext.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful types.HpkeCiphertext
  types.HpkeCiphertext.Insts.Tls_codecSpecIoRoundTripStd
  := by
  exact RoundTripStd.lawful_of_rtStd _ types.HpkeCiphertext.Insts.Tls_codecSerialize.Lawful
    types.HpkeCiphertext.Insts.Tls_codecDeserialize.Lawful
    types.HpkeCiphertext.Insts.CoreCmpPartialEqHpkeCiphertext.Lawful
    HC.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem types.HpkeCiphertext.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful types.HpkeCiphertext
  types.HpkeCiphertext.Insts.Tls_codecSpecIoNonEmptyStd
  := NonEmptyStd.lawful_of_rtStd _ types.HpkeCiphertext.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    HC.rtStd (by omega) rfl

theorem types.SignatureScheme.Insts.CoreCmpPartialEqSignatureScheme.Lawful :
  core.cmp.PartialEq.Lawful types.SignatureScheme types.SignatureScheme
  types.SignatureScheme.Insts.CoreCmpPartialEqSignatureScheme
  := by
  derive_eq_lawful [types.SignatureScheme.Insts.CoreCmpPartialEqSignatureScheme.eq] []

theorem types.VerifiableCiphersuite.Insts.CoreCmpPartialEqVerifiableCiphersuite.Lawful
  :
  core.cmp.PartialEq.Lawful types.VerifiableCiphersuite
  types.VerifiableCiphersuite
  types.VerifiableCiphersuite.Insts.CoreCmpPartialEqVerifiableCiphersuite
  := by
  derive_eq_lawful [types.VerifiableCiphersuite.Insts.CoreCmpPartialEqVerifiableCiphersuite.eq] []

theorem types.Ciphersuite.Insts.CoreCmpPartialEqCiphersuite.Lawful :
  core.cmp.PartialEq.Lawful types.Ciphersuite types.Ciphersuite
  types.Ciphersuite.Insts.CoreCmpPartialEqCiphersuite
  := by
  derive_eq_lawful [types.Ciphersuite.Insts.CoreCmpPartialEqCiphersuite.eq] []

theorem types.SignatureScheme.Insts.Tls_codecSpecRoundTrip.Lawful :
  tls_codec.spec.RoundTrip.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecSpecRoundTrip
  := by
  derive_rt_lawful types.SignatureScheme.Insts.Tls_codecSerializeBytes.Lawful
    types.SignatureScheme.Insts.Tls_codecDeserializeBytes.Lawful
    types.SignatureScheme.Insts.CoreCmpPartialEqSignatureScheme.Lawful
    [types.SignatureScheme.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
     types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ECDSA_SECP256R1_SHA256,
     types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ECDSA_SECP384R1_SHA384,
     types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ECDSA_SECP521R1_SHA512,
     types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ED25519,
     types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ED448]
    [types.SignatureScheme.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes]
    [tls_codec.U16.Insts.Tls_codecSpecRoundTrip.Lawful]

theorem types.SignatureScheme.Insts.Tls_codecSpecNonEmpty.Lawful :
  tls_codec.spec.NonEmpty.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecSpecNonEmpty
  := by
  derive_ne_lawful types.SignatureScheme.Insts.Tls_codecSpecRoundTrip.Lawful
    [types.SignatureScheme.Insts.Tls_codecSerializeBytes.tls_serialize_bytes,
     types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ECDSA_SECP256R1_SHA256,
     types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ECDSA_SECP384R1_SHA384,
     types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ECDSA_SECP521R1_SHA512,
     types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ED25519,
     types.SerializeBytesSignatureScheme.tls_serialize_bytes.__TLS_CODEC_ED448]
    [tls_codec.U16.Insts.Tls_codecSpecNonEmpty.Lawful] []

set_option maxHeartbeats 2000000 in
private theorem SS.rtStd : RtStd types.SignatureScheme.Insts.Tls_codecSerialize
    types.SignatureScheme.Insts.Tls_codecDeserialize 2 2 := by
  derive_rt_std (by have := imax_ge; omega) types.SignatureScheme.Insts.Tls_codecSize.Lawful
    [types.SignatureScheme.Insts.Tls_codecSerialize.tls_serialize,
    types.SerializeSignatureScheme.tls_serialize.__TLS_CODEC_ECDSA_SECP256R1_SHA256,
    types.SerializeSignatureScheme.tls_serialize.__TLS_CODEC_ECDSA_SECP384R1_SHA384,
    types.SerializeSignatureScheme.tls_serialize.__TLS_CODEC_ECDSA_SECP521R1_SHA512,
    types.SerializeSignatureScheme.tls_serialize.__TLS_CODEC_ED25519,
    types.SerializeSignatureScheme.tls_serialize.__TLS_CODEC_ED448, add_zero_u16, cast_u16_self]
    [types.SignatureScheme.Insts.Tls_codecSize, types.SignatureScheme.Insts.Tls_codecSize.tls_serialized_len]
    [types.SignatureScheme.Insts.Tls_codecDeserialize.tls_deserialize] [] [U16.rtStd]

private theorem VC.rtStd : RtStd types.VerifiableCiphersuite.Insts.Tls_codecSerialize
    types.VerifiableCiphersuite.Insts.Tls_codecDeserialize 2 2 := by
  derive_rt_std (by have := imax_ge; omega) types.VerifiableCiphersuite.Insts.Tls_codecSize.Lawful
    [types.VerifiableCiphersuite.Insts.Tls_codecSerialize.tls_serialize,
     Shared0VerifiableCiphersuite.Insts.Tls_codecSize.tls_serialized_len]
    [types.VerifiableCiphersuite.Insts.Tls_codecSize, types.VerifiableCiphersuite.Insts.Tls_codecSize.tls_serialized_len]
    [types.VerifiableCiphersuite.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.U16.Insts.Tls_codecSize.Lawful] [U16.rtStd]

set_option maxHeartbeats 4000000 in
private theorem CS.rtStd : RtStd types.Ciphersuite.Insts.Tls_codecSerialize
    types.Ciphersuite.Insts.Tls_codecDeserialize 2 2 := by
  derive_rt_std (by have := imax_ge; omega) types.Ciphersuite.Insts.Tls_codecSize.Lawful
    [types.Ciphersuite.Insts.Tls_codecSerialize.tls_serialize,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_128_DHKEMP256_AES128GCM_SHA256_P256,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_128_DHKEMX25519_AES128GCM_SHA256_Ed25519,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_128_DHKEMX25519_CHACHA20POLY1305_SHA256_Ed25519,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_256_DHKEMP384_AES256GCM_SHA384_P384,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_256_DHKEMP521_AES256GCM_SHA512_P521,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_256_DHKEMX448_AES256GCM_SHA512_Ed448,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_256_DHKEMX448_CHACHA20POLY1305_SHA512_Ed448,
    add_zero_u16, cast_u16_self]
    [types.Ciphersuite.Insts.Tls_codecSize, types.Ciphersuite.Insts.Tls_codecSize.tls_serialized_len]
    [types.Ciphersuite.Insts.Tls_codecDeserialize.tls_deserialize] [] [U16.rtStd]

theorem types.SignatureScheme.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ types.SignatureScheme.Insts.Tls_codecSerialize.Lawful
    types.SignatureScheme.Insts.Tls_codecDeserialize.Lawful
    types.SignatureScheme.Insts.CoreCmpPartialEqSignatureScheme.Lawful SS.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem types.SignatureScheme.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ types.SignatureScheme.Insts.Tls_codecSpecIoRoundTripStd.Lawful SS.rtStd (by omega) rfl

theorem types.VerifiableCiphersuite.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful types.VerifiableCiphersuite
  types.VerifiableCiphersuite.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ types.VerifiableCiphersuite.Insts.Tls_codecSerialize.Lawful
    types.VerifiableCiphersuite.Insts.Tls_codecDeserialize.Lawful
    types.VerifiableCiphersuite.Insts.CoreCmpPartialEqVerifiableCiphersuite.Lawful VC.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem types.VerifiableCiphersuite.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful types.VerifiableCiphersuite
  types.VerifiableCiphersuite.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ types.VerifiableCiphersuite.Insts.Tls_codecSpecIoRoundTripStd.Lawful VC.rtStd (by omega) rfl

theorem types.Ciphersuite.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful types.Ciphersuite
  types.Ciphersuite.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ types.Ciphersuite.Insts.Tls_codecSerialize.Lawful
    types.Ciphersuite.Insts.Tls_codecDeserialize.Lawful
    types.Ciphersuite.Insts.CoreCmpPartialEqCiphersuite.Lawful CS.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem types.Ciphersuite.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful types.Ciphersuite
  types.Ciphersuite.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ types.Ciphersuite.Insts.Tls_codecSpecIoRoundTripStd.Lawful CS.rtStd (by omega) rfl

theorem types.HpkePrivateKey.Insts.CoreCmpPartialEqHpkePrivateKey.Lawful :
  core.cmp.PartialEq.Lawful types.HpkePrivateKey types.HpkePrivateKey
  types.HpkePrivateKey.Insts.CoreCmpPartialEqHpkePrivateKey
  := by
  derive_eq_lawful [types.HpkePrivateKey.Insts.CoreCmpPartialEqHpkePrivateKey.eq]
    [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.CoreCmpPartialEqSecretVLBytes.Lawful]

private theorem HPK.rtStd : RtStd types.HpkePrivateKey.Insts.Tls_codecSerialize
    types.HpkePrivateKey.Insts.Tls_codecDeserialize 1 (2 ^ 30 + 3) := by
  derive_rt_std_flat (by have := imax_ge; omega) types.HpkePrivateKey.Insts.Tls_codecSize.Lawful
    [types.HpkePrivateKey.Insts.Tls_codecSerialize.tls_serialize, Shared0HpkePrivateKey.Insts.Tls_codecSize.tls_serialized_len]
    [types.HpkePrivateKey.Insts.Tls_codecSize, types.HpkePrivateKey.Insts.Tls_codecSize.tls_serialized_len]
    [types.HpkePrivateKey.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSize.Lawful]
    [SecretVLBytes.rtStd]

theorem types.HpkePrivateKey.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful types.HpkePrivateKey
  types.HpkePrivateKey.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ types.HpkePrivateKey.Insts.Tls_codecSerialize.Lawful
    types.HpkePrivateKey.Insts.Tls_codecDeserialize.Lawful
    types.HpkePrivateKey.Insts.CoreCmpPartialEqHpkePrivateKey.Lawful HPK.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem types.HpkePrivateKey.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful types.HpkePrivateKey
  types.HpkePrivateKey.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ types.HpkePrivateKey.Insts.Tls_codecSpecIoRoundTripStd.Lawful HPK.rtStd (by omega) rfl


/-! ## Agreement of the decoders (`DecodersAgree`) and the mixed round trip (`RoundTripMixed`)

Each type's `std` and byte-slice decoders agree (TlsCodec's `Derive/DecodersAgree.lean`): derived
structs and newtypes are chains of field decoders (`seqStd` / `seqB`, equal to the extraction by
`seq_std_eq` / `seq_b_eq`) over the fields' facts; derived `u16` enums by `enum_agree_vcs` /
`enum_bindep`. The mixed round trip follows from the `std` round trip (`RoundTripMixed.lawful_of`). -/

theorem types.SignatureScheme.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ types.SignatureScheme.Insts.Tls_codecDeserialize.Lawful
    types.SignatureScheme.Insts.Tls_codecDeserializeBytes.Lawful
    types.SignatureScheme.Insts.CoreCmpPartialEqSignatureScheme.Lawful
    (by
      intro R RI v a law r
      have hU := U16.agree.1 R RI v a law r
      mvcgen [types.SignatureScheme.Insts.Tls_codecDeserialize.tls_deserialize, hU]
      enum_agree_vcs types.SignatureScheme.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes)
    (by
      enum_bindep types.SignatureScheme.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
        U16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, U16.agree)
    (fun _ => rfl) rfl

theorem types.SignatureScheme.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful types.SignatureScheme
  types.SignatureScheme.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ types.SignatureScheme.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    types.SignatureScheme.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem types.HpkeCiphertext.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful types.HpkeCiphertext
  types.HpkeCiphertext.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ types.HpkeCiphertext.Insts.Tls_codecDeserialize.Lawful
    types.HpkeCiphertext.Insts.Tls_codecDeserializeBytes.Lawful
    types.HpkeCiphertext.Insts.CoreCmpPartialEqHpkeCiphertext.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun x =>
      AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun y =>
        AgreeF.ret ({ kem_output := x, ciphertext := y } : types.HpkeCiphertext))
      (fun _ _ _ => by seq_std_eq types.HpkeCiphertext.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq types.HpkeCiphertext.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
      (fun x => BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun y => BIndepF.ret ({ kem_output := x, ciphertext := y } : types.HpkeCiphertext)) (Agree.total VLBytes.agree.1))
      (Agree.total VLBytes.agree.1))
      (fun _ => by seq_b_eq types.HpkeCiphertext.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem types.HpkeCiphertext.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful types.HpkeCiphertext
  types.HpkeCiphertext.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ types.HpkeCiphertext.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    types.HpkeCiphertext.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem types.VerifiableCiphersuite.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful types.VerifiableCiphersuite
  types.VerifiableCiphersuite.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ types.VerifiableCiphersuite.Insts.Tls_codecDeserialize.Lawful
    types.VerifiableCiphersuite.Insts.Tls_codecDeserializeBytes.Lawful
    types.VerifiableCiphersuite.Insts.CoreCmpPartialEqVerifiableCiphersuite.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree U16.agree.1) fun x =>
      AgreeF.ret (x : types.VerifiableCiphersuite))
      (fun _ _ _ => by seq_std_eq types.VerifiableCiphersuite.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq types.VerifiableCiphersuite.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep U16.agree.2)
      (fun x => BIndepF.ret (x : types.VerifiableCiphersuite)) (Agree.total U16.agree.1))
      (fun _ => by seq_b_eq types.VerifiableCiphersuite.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem types.VerifiableCiphersuite.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful types.VerifiableCiphersuite
  types.VerifiableCiphersuite.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ types.VerifiableCiphersuite.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    types.VerifiableCiphersuite.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem types.Ciphersuite.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful types.Ciphersuite
  types.Ciphersuite.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ types.Ciphersuite.Insts.Tls_codecDeserialize.Lawful
    types.Ciphersuite.Insts.Tls_codecDeserializeBytes.Lawful
    types.Ciphersuite.Insts.CoreCmpPartialEqCiphersuite.Lawful
    (by
      intro R RI v a law r
      have hU := U16.agree.1 R RI v a law r
      mvcgen [types.Ciphersuite.Insts.Tls_codecDeserialize.tls_deserialize, hU]
      enum_agree_vcs types.Ciphersuite.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes)
    (by
      enum_bindep types.Ciphersuite.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
        U16.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, U16.agree)
    (fun _ => rfl) rfl

theorem types.Ciphersuite.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful types.Ciphersuite
  types.Ciphersuite.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ types.Ciphersuite.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    types.Ciphersuite.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem types.HpkePrivateKey.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful types.HpkePrivateKey
  types.HpkePrivateKey.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ types.HpkePrivateKey.Insts.Tls_codecDeserialize.Lawful
    types.HpkePrivateKey.Insts.Tls_codecDeserializeBytes.Lawful
    types.HpkePrivateKey.Insts.CoreCmpPartialEqHpkePrivateKey.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree SecretVLBytes.agree.1) fun x =>
      AgreeF.ret (x : types.HpkePrivateKey))
      (fun _ _ _ => by seq_std_eq types.HpkePrivateKey.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq types.HpkePrivateKey.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep SecretVLBytes.agree.2)
      (fun x => BIndepF.ret (x : types.HpkePrivateKey)) (Agree.total SecretVLBytes.agree.1))
      (fun _ => by seq_b_eq types.HpkePrivateKey.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem types.HpkePrivateKey.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful types.HpkePrivateKey
  types.HpkePrivateKey.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ types.HpkePrivateKey.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    types.HpkePrivateKey.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

end openmls_traits
