/- Crate-specific instantiations of TlsCodec's `std` helpers (`Verification/Derive/Std.lean`) for the
derived impls of `openmls_traits::types`: the `u16` enums
`VerifiableCiphersuite`, `SignatureScheme`, `Ciphersuite` and the newtype `HpkePrivateKey`; and the
round-trip fact `RtStd` of `SecretVLBytes` (the field of `HpkePrivateKey` and of `openmls_basic_credential`'s
`SignatureKeyPair`), transported from TlsCodec's `VLBytes.rtStd`.

Obligations: none directly; their `Serialize` / `Deserialize` / round-trip obligations in
`ProofObligations.lean` use them.
Axioms reached (`scripts/axiom_whitelist.txt`): ASSUMED `size_of`, `size_of_U16`; 1 signature-only
stub (`core.io.error.Error.Insts.CoreFmtDebug.fmt`). -/
import Aeneas
import CoreModels
import Hax
import TraitsCodec.Extraction
import TlsCodec.Verification.ProofObligations
import TlsCodec.Verification.Derive.Std
import TlsCodec.Verification.Derive.RoundTripStd
import TlsCodec.Verification.Derive.DecodersAgree
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

theorem VC.ser_runs (x : types.VerifiableCiphersuite) :
    SerRuns types.VerifiableCiphersuite.Insts.Tls_codecSerialize x 2#usize
      (some (Aeneas.Std.core.num.U16.to_be_bytes x).val) := by
  intro W WI hWI w hroom
  obtain ⟨r, w1, hr, hs, -⟩ := U16.ser_runs x W WI hWI w hroom
  obtain ⟨⟨n, rfl, hn⟩, hv⟩ := hs _ rfl
  have hl : (Aeneas.Std.core.num.U16.to_be_bytes x).val.length = 2 := by
    simp
  have hn2 : n = 2#usize := UScalar.eq_of_val_eq (by rw [hn, hl]; rfl)
  subst hn2
  refine ⟨.Ok 2#usize, w1, ?_, fun b hb => ?_, fun h => by cases h⟩
  · have hr' : tls_codec.U16.Insts.Tls_codecSerialize.tls_serialize WI x w =
        ok (.Ok 2#usize, w1) := hr
    simp only [types.VerifiableCiphersuite.Insts.Tls_codecSerialize.tls_serialize, hr',
      Shared0VerifiableCiphersuite.Insts.Tls_codecSize.tls_serialized_len,
      types.VerifiableCiphersuite.Insts.Tls_codecSize.tls_serialized_len,
      U16.Insts.Tls_codecSize.tls_serialized_len, len_add_ok, lenAdd_0_2, bind_tc_ok,
      Aeneas.Std.bind_ok]
    simp [core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch, zero_add_ok,
      lenAdd_0_2]
  · cases hb; exact ⟨⟨2#usize, rfl, hl.symm⟩, hv⟩

theorem VC.size (x : types.VerifiableCiphersuite) :
    types.VerifiableCiphersuite.Insts.Tls_codecSize.tls_serialized_len x = ok 2#usize := by
  simp [types.VerifiableCiphersuite.Insts.Tls_codecSize.tls_serialized_len,
    U16.Insts.Tls_codecSize.tls_serialized_len, len_add_ok, lenAdd_0_2]

theorem VC.de_runs : DeRuns types.VerifiableCiphersuite.Insts.Tls_codecDeserialize
    (fun _ _ _ => True) := by
  intro R RI v a law r
  have hT := U16.de_runs R RI v a law r
  mvcgen [types.VerifiableCiphersuite.Insts.Tls_codecDeserialize.tls_deserialize, hT]
  · rename_i p hp _ u _ hcf
    intro val hval; cases hval
    obtain ⟨n, sz, hn, h2, hsz, hszn, -⟩ := hp u (continue_eq_tryCF.mp hcf)
    have hu : U16.Insts.Tls_codecSize.tls_serialized_len u = ok 2#usize := by
      simp [U16.Insts.Tls_codecSize.tls_serialized_len]
    rw [hu] at hsz; ok_cases hsz
    exact ⟨n, 2#usize, hn, h2, VC.size u, hszn⟩
  · rename_i q _ _ res _ hbr
    refine try_break_vc (x := q.1) (fun e _ => ?_) hbr
    mvcgen
    intro _
    mvcgen
    all_goals simp

theorem SS.ser (x : types.SignatureScheme) :
    ∃ sz b, types.SignatureScheme.Insts.Tls_codecSerialize.SizeInst.tls_serialized_len x = ok sz ∧
      sz.val ≤ imax ∧ b.length = sz.val ∧
      SerRuns types.SignatureScheme.Insts.Tls_codecSerialize x sz (some b) := by
  u16_enum_ser types.SignatureScheme.Insts.Tls_codecSerialize, x [
    types.SignatureScheme.Insts.Tls_codecSerialize,
    types.SignatureScheme.Insts.Tls_codecSerialize.tls_serialize,
    types.SerializeSignatureScheme.tls_serialize.__TLS_CODEC_ECDSA_SECP256R1_SHA256,
    types.SerializeSignatureScheme.tls_serialize.__TLS_CODEC_ECDSA_SECP384R1_SHA384,
    types.SerializeSignatureScheme.tls_serialize.__TLS_CODEC_ECDSA_SECP521R1_SHA512,
    types.SerializeSignatureScheme.tls_serialize.__TLS_CODEC_ED25519,
    types.SerializeSignatureScheme.tls_serialize.__TLS_CODEC_ED448]

theorem SS.de_runs : DeRuns types.SignatureScheme.Insts.Tls_codecDeserialize
    (fun _ _ _ => True) := by
  u16_enum_de [types.SignatureScheme.Insts.Tls_codecDeserialize.tls_deserialize]

theorem CS.ser (x : types.Ciphersuite) :
    ∃ sz b, types.Ciphersuite.Insts.Tls_codecSerialize.SizeInst.tls_serialized_len x = ok sz ∧
      sz.val ≤ imax ∧ b.length = sz.val ∧
      SerRuns types.Ciphersuite.Insts.Tls_codecSerialize x sz (some b) := by
  u16_enum_ser types.Ciphersuite.Insts.Tls_codecSerialize, x [
    types.Ciphersuite.Insts.Tls_codecSerialize,
    types.Ciphersuite.Insts.Tls_codecSerialize.tls_serialize,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_256_DHKEMP384_AES256GCM_SHA384_P384,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_256_DHKEMX448_CHACHA20POLY1305_SHA512_Ed448,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_256_DHKEMP521_AES256GCM_SHA512_P521,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_256_DHKEMX448_AES256GCM_SHA512_Ed448,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_128_DHKEMX25519_CHACHA20POLY1305_SHA256_Ed25519,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_128_DHKEMP256_AES128GCM_SHA256_P256,
    types.SerializeCiphersuite.tls_serialize.__TLS_CODEC_MLS_128_DHKEMX25519_AES128GCM_SHA256_Ed25519]

theorem CS.de_runs : DeRuns types.Ciphersuite.Insts.Tls_codecDeserialize
    (fun _ _ _ => True) := by
  u16_enum_de [types.Ciphersuite.Insts.Tls_codecDeserialize.tls_deserialize]

theorem HPK.ser_runs (x : types.HpkePrivateKey) (s : Std.Usize)
    (hs : quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSize.tls_serialized_len x = ok s) :
    SerRuns types.HpkePrivateKey.Insts.Tls_codecSerialize x s
      (encOut quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSerialize x) := by
  newtype_ser quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSerialize, x, x,
    quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSerialize.Lawful, s, hs,
    types.HpkePrivateKey.Insts.Tls_codecSerialize.tls_serialize,
    Shared0HpkePrivateKey.Insts.Tls_codecSize.tls_serialized_len,
    types.HpkePrivateKey.Insts.Tls_codecSize.tls_serialized_len

theorem HPK.size (x : types.HpkePrivateKey) (s : Std.Usize)
    (hs : quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSize.tls_serialized_len x = ok s) :
    types.HpkePrivateKey.Insts.Tls_codecSize.tls_serialized_len x = ok s := by
  simp [types.HpkePrivateKey.Insts.Tls_codecSize.tls_serialized_len, hs, len_add_ok, lenAdd_0]

theorem HPK.de_runs : DeRuns types.HpkePrivateKey.Insts.Tls_codecDeserialize
    (fun _ _ _ => True) := by
  newtype_de quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecDeserialize.Lawful,
    types.HpkePrivateKey.Insts.Tls_codecDeserialize.tls_deserialize, HPK.size

/-- `SecretVLBytes`: as `VLBytes` (same serializer and size, same decoder up to the rewrapping). -/
theorem SecretVLBytes.rtStd : RtStd quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSerialize
    quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecDeserialize 1 (2 ^ 30 + 3) := by
  have h := VLBytes.rtStd
  refine ⟨h.room, fun x W WI hWI w hr => h.ser x W WI hWI w hr, fun x b hb => h.bound x b hb,
    fun x b hb => h.lo x b hb, fun x b hb R RI v a law r rest hv => ?_⟩
  simp only [SecretVLBytes.de_eq]
  exact h.dec x b hb R RI v a law r rest hv

end openmls_traits
