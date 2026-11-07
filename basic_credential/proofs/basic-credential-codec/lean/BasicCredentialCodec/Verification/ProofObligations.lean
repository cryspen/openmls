/- The per-impl `Lawful` obligations of the tls_codec impls of `SignatureKeyPair`, statements exactly
as generated in `Extraction/ProofObligations.lean` (checked by `scripts/check_statements.py`). Each
proof is one call of TlsCodec's derive tactics (`Verification/Derive/Bytes.lean`,
`Verification/Derive/Std.lean`, `Verification/Derive/RoundTripStd.lean` for the round trip of
`src/codec_specs.rs`, whose `PartialEq` is derived under `cfg(hax)` only).

Obligations: all 9 of `Extraction/ProofObligations.lean`.
Axioms reached (`scripts/axiom_whitelist.txt`): ASSUMED `size_of`, `size_of_U16`, `size_of_U8`,
`numBits_eq_64` (the round trip's bound, `imax_64`); 1 signature-only stub
(`core.io.error.Error.Insts.CoreFmtDebug.fmt`). -/
import BasicCredentialCodec.Extraction
import TlsCodec.Verification.ProofObligations
import TlsCodec.Verification.Derive.Std
import TlsCodec.Verification.Derive.RoundTripStd
import TlsCodec.Verification.Derive.DecodersAgree
import TraitsCodec.Verification.ProofObligations
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace openmls_basic_credential
open tls_codec tls_codec.Derive

theorem SignatureKeyPair.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful SignatureKeyPair SignatureKeyPair.Insts.Tls_codecSize
  :=
  by derive_size_lawful [SignatureKeyPair.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSize.Lawful, (tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ tls_codec.U8.Insts.Tls_codecSize.Lawful), openmls_traits.types.SignatureScheme.Insts.Tls_codecSize.Lawful]

theorem SignatureKeyPair.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful SignatureKeyPair
  SignatureKeyPair.Insts.Tls_codecSerialize
  :=
  by derive_ser_std_lawful SignatureKeyPair.Insts.Tls_codecSize.Lawful
    [SignatureKeyPair.Insts.Tls_codecSerialize.tls_serialize, Shared0SignatureKeyPair.Insts.Tls_codecSize.tls_serialized_len]
    [SignatureKeyPair.Insts.Tls_codecSize, SignatureKeyPair.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSerialize.Lawful,
      (tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize.Lawful _ core.U8.Insts.CoreFmtDebug
        tls_codec.U8.Insts.Tls_codecSerialize.Lawful ⟨⟩),
      openmls_traits.types.SignatureScheme.Insts.Tls_codecSerialize.Lawful]

theorem SignatureKeyPair.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful SignatureKeyPair
  SignatureKeyPair.Insts.Tls_codecDeserialize
  :=
  by derive_de_std_lawful SignatureKeyPair.Insts.Tls_codecSize.Lawful
    [SignatureKeyPair.Insts.Tls_codecDeserialize.tls_deserialize]
    [SignatureKeyPair.Insts.Tls_codecSize, SignatureKeyPair.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecDeserialize.Lawful,
      (tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize.Lawful _ tls_codec.U8.Insts.Tls_codecDeserialize.Lawful),
      openmls_traits.types.SignatureScheme.Insts.Tls_codecDeserialize.Lawful]

theorem SignatureKeyPair.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful SignatureKeyPair
  SignatureKeyPair.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful SignatureKeyPair.Insts.Tls_codecSize.Lawful [SignatureKeyPair.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, SignatureKeyPair.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecDeserializeBytes.Lawful, tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.Lawful _ tls_codec.U8.Insts.Tls_codecDeserializeBytes.Lawful, openmls_traits.types.SignatureScheme.Insts.Tls_codecDeserializeBytes.Lawful]

/-! ## Round trip (`src/codec_specs.rs`) -/

theorem SignatureKeyPair.Insts.CoreCmpPartialEqSignatureKeyPair.Lawful :
  core.cmp.PartialEq.Lawful SignatureKeyPair SignatureKeyPair
  SignatureKeyPair.Insts.CoreCmpPartialEqSignatureKeyPair
  := by
  derive_eq_lawful [SignatureKeyPair.Insts.CoreCmpPartialEqSignatureKeyPair.eq]
    [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.CoreCmpPartialEqSecretVLBytes.Lawful,
      (tls_codec.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.Lawful _ core.U8.Insts.CoreCmpPartialEqU8.Lawful),
      openmls_traits.types.SignatureScheme.Insts.CoreCmpPartialEqSignatureScheme.Lawful]

private theorem SS.size2 (x : openmls_traits.types.SignatureScheme) :
    openmls_traits.types.SignatureScheme.Insts.Tls_codecSize.tls_serialized_len x = ok 2#usize := by
  simp only [openmls_traits.types.SignatureScheme.Insts.Tls_codecSize.tls_serialized_len]
  exact tls_codec.Derive.u16_enum_size

/-- `SignatureScheme` (`openmls_traits`, a `u16` enum): its 2 bytes, from its round-trip
obligation. -/
private theorem SS.rtStd : RtStd openmls_traits.types.SignatureScheme.Insts.Tls_codecSerialize
    openmls_traits.types.SignatureScheme.Insts.Tls_codecDeserialize 2 2 := by
  have := imax_ge
  have hL := openmls_traits.types.SignatureScheme.Insts.Tls_codecSerialize.Lawful
  refine RtStd.of_const hL (by omega) (fun x => by rw [szv_eq (SS.size2 x)]; simp)
    (fun x b hb => ?_)
    (rt_decodes_out openmls_traits.types.SignatureScheme.Insts.Tls_codecSpecIoRoundTripStd.Lawful)
  rw [Serialize.Lawful.enc_len hL x _ (SS.size2 x) (by simp; omega) b hb]
  simp

set_option maxHeartbeats 2000000 in
private theorem SKP.rtStd : RtStd SignatureKeyPair.Insts.Tls_codecSerialize
    SignatureKeyPair.Insts.Tls_codecDeserialize (1 + 1 + 2) (2 ^ 30 + 3 + (2 ^ 30 + 3) + 2) := by
  derive_rt_std (by have := imax_64; omega) SignatureKeyPair.Insts.Tls_codecSize.Lawful
    [SignatureKeyPair.Insts.Tls_codecSerialize.tls_serialize, Shared0SignatureKeyPair.Insts.Tls_codecSize.tls_serialized_len]
    [SignatureKeyPair.Insts.Tls_codecSize, SignatureKeyPair.Insts.Tls_codecSize.tls_serialized_len]
    [SignatureKeyPair.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSize.Lawful,
      (tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ tls_codec.U8.Insts.Tls_codecSize.Lawful),
      openmls_traits.types.SignatureScheme.Insts.Tls_codecSize.Lawful]
    [openmls_traits.SecretVLBytes.rtStd,
      (Vec.rtStd tls_codec.U8.Insts.Tls_codecSpecIoNonEmptyStd core.U8.Insts.CoreFmtDebug
        tls_codec.U8.Insts.Tls_codecSpecIoNonEmptyStd.Lawful ⟨⟩),
      SS.rtStd]

theorem SignatureKeyPair.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful SignatureKeyPair
  SignatureKeyPair.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ SignatureKeyPair.Insts.Tls_codecSerialize.Lawful
    SignatureKeyPair.Insts.Tls_codecDeserialize.Lawful
    SignatureKeyPair.Insts.CoreCmpPartialEqSignatureKeyPair.Lawful SKP.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem SignatureKeyPair.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful SignatureKeyPair
  SignatureKeyPair.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ SignatureKeyPair.Insts.Tls_codecSpecIoRoundTripStd.Lawful SKP.rtStd (by omega) rfl

/-! ## Agreement of the decoders (`DecodersAgree`) and the mixed round trip (`RoundTripMixed`)

The derived decoders are chains of the field decoders (TlsCodec's `Derive/DecodersAgree.lean`):
`SecretVLBytes`, `Vec<u8>` and `SignatureScheme` (whose facts come from its `DecodersAgree`). -/

theorem SignatureKeyPair.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful SignatureKeyPair
  SignatureKeyPair.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ SignatureKeyPair.Insts.Tls_codecDeserialize.Lawful
    SignatureKeyPair.Insts.Tls_codecDeserializeBytes.Lawful
    SignatureKeyPair.Insts.CoreCmpPartialEqSignatureKeyPair.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree SecretVLBytes.agree.1) fun x =>
      AgreeF.seq (AgreeF.of_agree (Vec.agree U8.Insts.Tls_codecDeserialize.Lawful U8.Insts.Tls_codecDeserializeBytes.Lawful U8.agree.1 U8.agree.2).1) fun y =>
        AgreeF.seq (AgreeF.of_agree openmls_traits.types.SignatureScheme.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree) fun z =>
          AgreeF.ret ({ «private» := x, «public» := y, signature_scheme := z } : SignatureKeyPair))
      (fun _ _ _ => by seq_std_eq SignatureKeyPair.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq SignatureKeyPair.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep SecretVLBytes.agree.2)
      (fun x => BIndepF.seq (BIndepF.of_bindep (Vec.agree U8.Insts.Tls_codecDeserialize.Lawful U8.Insts.Tls_codecDeserializeBytes.Lawful U8.agree.1 U8.agree.2).2)
        (fun y => BIndepF.seq (BIndepF.of_bindep openmls_traits.types.SignatureScheme.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep)
          (fun z => BIndepF.ret ({ «private» := x, «public» := y, signature_scheme := z } : SignatureKeyPair))
          (Agree.total openmls_traits.types.SignatureScheme.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree))
        (Agree.total (Vec.agree U8.Insts.Tls_codecDeserialize.Lawful U8.Insts.Tls_codecDeserializeBytes.Lawful U8.agree.1 U8.agree.2).1))
      (Agree.total SecretVLBytes.agree.1))
      (fun _ => by seq_b_eq SignatureKeyPair.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem SignatureKeyPair.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful SignatureKeyPair
  SignatureKeyPair.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ SignatureKeyPair.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    SignatureKeyPair.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

end openmls_basic_credential
