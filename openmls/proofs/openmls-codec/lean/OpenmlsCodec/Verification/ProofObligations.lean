/- The per-impl `Lawful` obligations of the tls_codec impls of `openmls` (versions, ciphersuite,
credentials, extensions), statements exactly as generated in `Extraction/ProofObligations.lean`
(checked by `scripts/check_statements.py`). The derived impls are one call of TlsCodec's derive
tactics (`Verification/Derive/Bytes.lean`, `Verification/Derive/Std.lean`,
`Verification/Derive/RoundTripStd.lean`); the hand-written `Extension` / `Extensions<T>` codecs are
instantiations of `ExtensionStd.lean`, `ExtensionStdSer.lean` and `ExtensionsTryFrom.lean`, the
round trip of the hand-written `u16`-coded enums of `RoundTrip.lean`.

Obligations: all 195 of `Extraction/ProofObligations.lean`; 2 of them (`RatchetTreeExtension`'s `Size`
and `Deserialize` `Lawful`) are the ASSUMED axioms of `Assumptions/RatchetTreeSpecs.lean`.
Axioms reached (`scripts/axiom_whitelist.txt`): ASSUMED `size_of`, `size_of_U16`, `size_of_U8`,
`numBits_eq_64` (round-trip bounds above `2^31 - 1`),
`openmls.extensions.ratchet_tree_extension.RatchetTreeExtension.deserialize_lawful_assumed`,
`openmls.extensions.ratchet_tree_extension.RatchetTreeExtension.serialize_lawful_assumed`,
`openmls.extensions.ratchet_tree_extension.RatchetTreeExtension.size_lawful_assumed`, the 3
`…CoreFmtDebug.fmt.ok_spec` of `Assumptions/FmtAssumptions.lean` (the `Serialize` of
`CredentialType` / `ProposalType` / `ExtensionType` and what uses them),
`openmls.ciphersuite.equal_ct.spec` of `Assumptions/EqualCtSpec.lean` (`Secret`'s `PartialEq` and
its round trip); 11 signature-only stubs (`ciphersuite.equal_ct`,
`core.io.error.Error.Insts.CoreFmtDebug.fmt`,
`credentials.CredentialType.Insts.CoreFmtDebug.fmt`, `extensions.Extension.Insts.CoreFmtDebug.fmt`,
`extensions.ExtensionType.Insts.CoreFmtDebug.fmt`,
`extensions.external_sender_extension.ExternalSender.Insts.CoreFmtDebug.fmt`,
`extensions.ratchet_tree_extension.RatchetTreeExtension`,
`extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecDeserialize.tls_deserialize`,
`extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSerialize.tls_serialize`,
`extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize.tls_serialized_len`,
`messages.proposals.ProposalType.Insts.CoreFmtDebug.fmt`); `native_decide` (2). -/
import OpenmlsCodec.Extraction
import TlsCodec.Verification.ProofObligations
import TlsCodec.Verification.Derive.Std
import TlsCodec.Verification.Std.SecretFrom
import TraitsCodec.Verification.ProofObligations
import OpenmlsCodec.Assumptions.RatchetTreeSpecs
import OpenmlsCodec.Verification.ExtensionStdSer
import OpenmlsCodec.Verification.ExtensionsTryFrom
import OpenmlsCodec.Verification.CanonicalSer
import OpenmlsCodec.Assumptions.FmtAssumptions
import OpenmlsCodec.Assumptions.EqualCtSpec
import TlsCodec.Verification.Derive.HandWrittenReader
import OpenmlsCodec.Verification.RoundTrip
import OpenmlsCodec.Verification.DecodersAgree
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace openmls
open tls_codec tls_codec.Derive

/-! `debytes_via_reader` (hand-written `DeserializeBytes` returning the reader left by the `std`
deserializer, upstream since 2026-08) lives in TlsCodec's `Verification/Derive/HandWrittenReader.lean`. -/

/-- `is_grease_value` is total. -/
private theorem grease_ok (u : Std.U16) : ∃ b, openmls_traits.grease.is_grease_value u = ok b := by
  unfold openmls_traits.grease.is_grease_value; split <;> exact ⟨_, rfl⟩

/-- `PartialEq.Lawful` of a derived `PartialEq` of a `u16`-coded enum (`eqd` its `eq`): `eq` decides
`=`, case by case on the variants (fields compared with `u16`'s `==`). -/
macro "u16_enum_eq_lawful" inst:ident "," eqd:ident "," rd:ident : tactic => `(tactic| (
  have key : ∀ x y, ∃ b, $eqd x y = ok b ∧ (b = true ↔ x = y) := by
    intro x y
    cases x <;> cases y <;>
      simp [$eqd:ident, $rd:ident, core.U16.Insts.CoreCmpPartialEqU16] <;>
      first | decide | (rename_i a b; by_cases h : a = b <;> simp_all)
  constructor
  · intro x y
    obtain ⟨b, hb, hbv⟩ := key x y
    simp only [$inst:ident, hb]
    exact ok_triple_of (by rw [heq_iff_eq]; exact hbv)
  · intro x y
    obtain ⟨b, hb, -⟩ := key x y
    simp only [$inst:ident, core.cmp.PartialEq.ne.default, hb, bind_tc_ok]
    exact ok_triple_of trivial))

/-- `Serialize.Lawful` of a hand-written `u16`-coded enum serializer that rejects non-canonical
values (upstream 2026-08): `toU` / `fromU` the `From` conversions, `ser` / `serfn` the instance and
its function, `hEq` the type's `PartialEq.Lawful`, `dbg` its `Debug` instance, `okspec` the ASSUMED
`Debug::fmt` spec (`Assumptions/FmtAssumptions.lean`). -/
macro "canon_u16_ser" hS:term "," hEq:term "," toU:ident "," fromU:ident "," ser:ident ","
    serfn:ident "," dbg:ident "," okspec:term : tactic => `(tactic| (
  refine ser_lawful_u16_or_err _ $hS (fun _ => rfl) (fun x => ?_) (fun _ => rfl)
  obtain ⟨k, hk⟩ : ∃ k, $toU x = ok k := by
    unfold $toU:ident; split <;> exact ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, $fromU k = ok y := by
    unfold $fromU:ident; split
    all_goals first
      | exact ⟨_, rfl⟩
      | (obtain ⟨b, hb⟩ := grease_ok k; simp only [hb, bind_tc_ok]; split <;> exact ⟨_, rfl⟩)
  have hne := ne_default_eq $hEq y x
  obtain ⟨_, he, hbe⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (core.num.U16.to_be_bytes_spec k)
  by_cases hc : y = x
  · left
    refine ⟨Array.to_slice (Aeneas.Std.core.num.U16.to_be_bytes k), by simp [Array.to_slice],
      fun WI w w' hw => ?_⟩
    subst hc
    simp only [$ser:ident, $serfn:ident, hk, hy, hne, he, hbe, lift, bind_tc_ok, hw, ne_eq,
      not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
    rfl
  · right
    intro W WI w
    obtain ⟨⟨r0, f0⟩, hf, hr0⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp ($okspec x ())
    simp only at hr0
    subst hr0
    simp only [$ser:ident, $serfn:ident, hk, hy, hne, hc, bind_tc_ok, ne_eq, not_false_eq_true,
      decide_true, if_true, core.fmt.rt.Argument.new_debug, core.Shared0T.Insts.CoreFmtDebug,
      core.Shared0T.Insts.CoreFmtDebug.fmt, $dbg:ident, hf, core.fmt.rt.Argument.new_lower_hex,
      core.U16.Insts.CoreFmtLowerHex, core.U16.Insts.CoreFmtLowerHex.fmt, core.fmt.Arguments.new,
      alloc.fmt.format, core.hint.must_use]
    try exact ⟨_, rfl⟩))

/-- `Deserialize.Lawful` of a hand-written `u16`-coded enum deserializer (`read_exact` of 2 bytes,
`from_be_bytes`, then a total `From<u16>` `f`): it consumes 2 bytes, its size. -/
macro "u16_read_de" hS:term "," de:ident "," f:ident : tactic => `(tactic| (
  refine de_lawful_of_runs _ $hS (P := fun _ _ _ => True) ?_ (fun _ _ => rfl)
  intro R RI v a law r
  have hre := read_exact_spec law r
  have hf : ∀ u, ⦃ ⌜ True ⌝ ⦄ $f u ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := fun u => by
    have hy : ∃ y, $f u = ok y := by
      unfold $f:ident; split
      all_goals first
        | exact ⟨_, rfl⟩
        | (obtain ⟨b, hb⟩ := grease_ok u; simp only [hb, bind_tc_ok]; split <;> exact ⟨_, rfl⟩)
    obtain ⟨y, hy⟩ := hy; rw [hy]; exact ok_triple_of trivial
  mvcgen [$de:ident, hre, hf, core.num.U16.from_be_bytes_spec]
  · rename_i arr p hp _ _ _ _ hcf _ _ _
    intro val _
    have hl : (arr.to_slice_mut.1 : Slice Std.U8).val.length = 2 := to_slice_mut_len arr
    by_cases h1 : 2 ≤ (v r).length
    · rw [hp.1 (by rw [hl]; exact h1), hl]
      exact ⟨2, 2#usize, h1, rfl, rfl, rfl⟩
    · rw [hp.2 (by rw [hl]; omega)] at hcf; simp [tryCF] at hcf
  · rename_i arr p hp _ res _ hbr
    have hl : (arr.to_slice_mut.1 : Slice Std.U8).val.length = 2 := to_slice_mut_len arr
    refine try_break_vc (x := p.1) (fun e he => ?_) hbr
    by_cases h1 : 2 ≤ (v r).length
    · rw [hp.1 (by rw [hl]; exact h1)] at he; cases he
    · rw [hp.2 (by rw [hl]; omega)] at he; cases he
      rw [from_io_eof]
      refine ok_triple_of ?_
      mvcgen
      intro _ h; cases h))


theorem ciphersuite.secret.Secret.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful ciphersuite.secret.Secret
  ciphersuite.secret.Secret.Insts.Tls_codecSize
  :=
  by derive_size_lawful [ciphersuite.secret.Secret.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSize.Lawful]

theorem ciphersuite.secret.Secret.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful ciphersuite.secret.Secret
  ciphersuite.secret.Secret.Insts.Tls_codecSerialize
  := by
  refine ser_lawful_of_runs _ ciphersuite.secret.Secret.Insts.Tls_codecSize.Lawful
    (fun x => encOut quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSerialize x.value)
    (fun x => ?_) (fun _ => rfl)
  have hs := size_ok
    quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSize.Lawful x.value
  exact ⟨_, hs, fun hle => Serialize.Lawful.enc_len
    quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSerialize.Lawful x.value _ hs hle,
    Serialize.Lawful.runs quic_vec.secret_bytes.SecretVLBytes.Insts.Tls_codecSerialize.Lawful
      x.value _ hs⟩

/-- `Secret`'s `std` deserializer, with TlsCodec's `SecretVLBytes.from_size`. -/
theorem ciphersuite.secret.Secret.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful ciphersuite.secret.Secret
  ciphersuite.secret.Secret.Insts.Tls_codecDeserialize
  := by
  refine de_lawful_of_runs _ ciphersuite.secret.Secret.Insts.Tls_codecSize.Lawful
    (P := fun _ _ _ => True) ?_ (fun _ _ => rfl)
  intro R RI v a law r
  have hT := Deserialize.Lawful.runs (tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize.Lawful _
    tls_codec.U8.Insts.Tls_codecDeserialize.Lawful) R RI v a law r
  mvcgen [ciphersuite.secret.Secret.Insts.Tls_codecDeserialize.tls_deserialize, hT]
  · rename_i p _ u _ hcf hp
    obtain ⟨n, sz, hn, h2, hsz, hszn⟩ := hp u (continue_eq_tryCF.mp hcf)
    obtain ⟨s, hs, hss⟩ := tls_codec.SecretVLBytes.from_size u sz hsz
    have hsec : ciphersuite.secret.Secret.Insts.Tls_codecSize.tls_serialized_len ⟨s⟩ = ok sz := by
      simp only [ciphersuite.secret.Secret.Insts.Tls_codecSize.tls_serialized_len, hss]
    rw [hs]
    mvcgen
    intro val hval
    cases hval
    exact ⟨n, sz, hn, h2, hsec, hszn⟩
  · rename_i q _ res _ hbr _
    refine try_break_vc (x := q.1) (fun e _ => ?_) hbr
    mvcgen
    intro _
    mvcgen
    all_goals simp

theorem ciphersuite.secret.Secret.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful ciphersuite.secret.Secret
  ciphersuite.secret.Secret.Insts.Tls_codecDeserializeBytes
  := by
  debytes_via_reader ciphersuite.secret.Secret.Insts.Tls_codecDeserializeBytes,
    ciphersuite.secret.Secret.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    ciphersuite.secret.Secret.Insts.Tls_codecDeserialize.Lawful, ciphersuite.secret.Secret.Insts.Tls_codecSize.Lawful

theorem ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful ciphersuite.hash_ref.HashReference
  ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize
  :=
  by derive_size_lawful [ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]

theorem
  ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful ciphersuite.hash_ref.HashReference
  ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.Lawful [ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.Lawful]

theorem ciphersuite.hash_ref.HashReference.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful ciphersuite.hash_ref.HashReference
  ciphersuite.hash_ref.HashReference.Insts.Tls_codecSerialize
  := by
  refine ser_lawful_of_runs _ ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.Lawful
    (fun x => encOut quic_vec.VLBytes.Insts.Tls_codecSerialize x.value) (fun x => ?_) (fun _ => rfl)
  have hs : quic_vec.VLBytes.Insts.Tls_codecSize.tls_serialized_len x.value =
      ok (szv quic_vec.VLBytes.Insts.Tls_codecSize x.value) :=
    size_ok quic_vec.VLBytes.Insts.Tls_codecSize.Lawful x.value
  refine ⟨_, ?_, fun hle => Serialize.Lawful.enc_len quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful
    x.value _ hs hle, ?_⟩
  · simp only [ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.tls_serialized_len]; rw [hs]
    simp [len_add_ok, lenAdd_0]
  · newtype_ser quic_vec.VLBytes.Insts.Tls_codecSerialize, x.value, x,
      quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful,
      (szv quic_vec.VLBytes.Insts.Tls_codecSize x.value), hs,
      ciphersuite.hash_ref.HashReference.Insts.Tls_codecSerialize.tls_serialize, Shared0HashReference.Insts.Tls_codecSize.tls_serialized_len,
      ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.tls_serialized_len

theorem ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful ciphersuite.hpke.EncryptContext
  ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize
  :=
  by derive_size_lawful [ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]

theorem ciphersuite.hpke.EncryptContext.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful ciphersuite.hpke.EncryptContext
  ciphersuite.hpke.EncryptContext.Insts.Tls_codecSerialize
  := by
  derive_ser_std_lawful ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize.Lawful
    [ciphersuite.hpke.EncryptContext.Insts.Tls_codecSerialize.tls_serialize, Shared0EncryptContext.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize, ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful]

theorem ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserializeBytes.Lawful
  :
  tls_codec.DeserializeBytes.Lawful ciphersuite.hpke.EncryptContext
  ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize.Lawful [ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.Lawful]

theorem ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful ciphersuite.reuse_guard.ReuseGuard
  ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize
  :=
  by derive_size_lawful [ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.tls_serialized_len] [(tls_codec.ArrayU8LEN.Insts.Tls_codecSize.Lawful 4#usize)]

theorem ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful ciphersuite.reuse_guard.ReuseGuard
  ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSerialize
  := by
  refine ser_lawful_of_runs _ ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.Lawful
    (fun x => encOut (ArrayU8LEN.Insts.Tls_codecSerialize 4#usize) x.value) (fun x => ?_) (fun _ => rfl)
  have hs : ArrayU8LEN.Insts.Tls_codecSize.tls_serialized_len x.value =
      ok (szv (ArrayU8LEN.Insts.Tls_codecSize 4#usize) x.value) :=
    size_ok (ArrayU8LEN.Insts.Tls_codecSize.Lawful 4#usize) x.value
  refine ⟨_, ?_, fun hle => Serialize.Lawful.enc_len (ArrayU8LEN.Insts.Tls_codecSerialize.Lawful 4#usize)
    x.value _ hs hle, ?_⟩
  · simp only [ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.tls_serialized_len]; rw [hs]
    simp [len_add_ok, lenAdd_0]
  · newtype_ser (ArrayU8LEN.Insts.Tls_codecSerialize 4#usize), x.value, x,
      (ArrayU8LEN.Insts.Tls_codecSerialize.Lawful 4#usize),
      (szv (ArrayU8LEN.Insts.Tls_codecSize 4#usize) x.value), hs,
      ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSerialize.tls_serialize, Shared0ReuseGuard.Insts.Tls_codecSize.tls_serialized_len,
      ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.tls_serialized_len

theorem
  ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful ciphersuite.reuse_guard.ReuseGuard
  ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.Lawful [ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.tls_serialized_len] [(tls_codec.ArrayU8LEN.Insts.Tls_codecDeserializeBytes.Lawful 4#usize)]

theorem ciphersuite.signature.Signature.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful ciphersuite.signature.Signature
  ciphersuite.signature.Signature.Insts.Tls_codecSize
  :=
  by derive_size_lawful [ciphersuite.signature.Signature.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]

theorem ciphersuite.signature.Signature.Insts.Tls_codecDeserializeBytes.Lawful
  :
  tls_codec.DeserializeBytes.Lawful ciphersuite.signature.Signature
  ciphersuite.signature.Signature.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful ciphersuite.signature.Signature.Insts.Tls_codecSize.Lawful [ciphersuite.signature.Signature.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, ciphersuite.signature.Signature.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.Lawful]

theorem ciphersuite.signature.Signature.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful ciphersuite.signature.Signature
  ciphersuite.signature.Signature.Insts.Tls_codecSerialize
  := by
  refine ser_lawful_of_runs _ ciphersuite.signature.Signature.Insts.Tls_codecSize.Lawful
    (fun x => encOut quic_vec.VLBytes.Insts.Tls_codecSerialize x.value) (fun x => ?_) (fun _ => rfl)
  have hs : quic_vec.VLBytes.Insts.Tls_codecSize.tls_serialized_len x.value =
      ok (szv quic_vec.VLBytes.Insts.Tls_codecSize x.value) :=
    size_ok quic_vec.VLBytes.Insts.Tls_codecSize.Lawful x.value
  refine ⟨_, ?_, fun hle => Serialize.Lawful.enc_len quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful
    x.value _ hs hle, ?_⟩
  · simp only [ciphersuite.signature.Signature.Insts.Tls_codecSize.tls_serialized_len]; rw [hs]
    simp [len_add_ok, lenAdd_0]
  · newtype_ser quic_vec.VLBytes.Insts.Tls_codecSerialize, x.value, x,
      quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful,
      (szv quic_vec.VLBytes.Insts.Tls_codecSize x.value), hs,
      ciphersuite.signature.Signature.Insts.Tls_codecSerialize.tls_serialize, Shared0Signature.Insts.Tls_codecSize.tls_serialized_len,
      ciphersuite.signature.Signature.Insts.Tls_codecSize.tls_serialized_len

theorem ciphersuite.signature.SignContent.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful ciphersuite.signature.SignContent
  ciphersuite.signature.SignContent.Insts.Tls_codecSize
  :=
  by derive_size_lawful [ciphersuite.signature.SignContent.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]

theorem ciphersuite.signature.SignContent.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful ciphersuite.signature.SignContent
  ciphersuite.signature.SignContent.Insts.Tls_codecSerialize
  := by
  derive_ser_std_lawful ciphersuite.signature.SignContent.Insts.Tls_codecSize.Lawful
    [ciphersuite.signature.SignContent.Insts.Tls_codecSerialize.tls_serialize, Shared0SignContent.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.signature.SignContent.Insts.Tls_codecSize, ciphersuite.signature.SignContent.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful]

theorem
  ciphersuite.signature.SignContent.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful ciphersuite.signature.SignContent
  ciphersuite.signature.SignContent.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful ciphersuite.signature.SignContent.Insts.Tls_codecSize.Lawful [ciphersuite.signature.SignContent.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, ciphersuite.signature.SignContent.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.Lawful]

theorem ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful ciphersuite.signature.SignaturePublicKey
  ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize
  :=
  by derive_size_lawful [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]

theorem
  ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful ciphersuite.signature.SignaturePublicKey
  ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSerialize
  := by
  refine ser_lawful_of_runs _ ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.Lawful
    (fun x => encOut quic_vec.VLBytes.Insts.Tls_codecSerialize x.value) (fun x => ?_) (fun _ => rfl)
  have hs : quic_vec.VLBytes.Insts.Tls_codecSize.tls_serialized_len x.value =
      ok (szv quic_vec.VLBytes.Insts.Tls_codecSize x.value) :=
    size_ok quic_vec.VLBytes.Insts.Tls_codecSize.Lawful x.value
  refine ⟨_, ?_, fun hle => Serialize.Lawful.enc_len quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful
    x.value _ hs hle, ?_⟩
  · simp only [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.tls_serialized_len]; rw [hs]
    simp [len_add_ok, lenAdd_0]
  · newtype_ser quic_vec.VLBytes.Insts.Tls_codecSerialize, x.value, x,
      quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful,
      (szv quic_vec.VLBytes.Insts.Tls_codecSize x.value), hs,
      ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSerialize.tls_serialize, Shared0SignaturePublicKey.Insts.Tls_codecSize.tls_serialized_len,
      ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.tls_serialized_len

theorem
  ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserializeBytes.Lawful
  :
  tls_codec.DeserializeBytes.Lawful ciphersuite.signature.SignaturePublicKey
  ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.Lawful [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.Lawful]

/-! `std` `Deserialize` of the derived ciphersuite types (generated obligations). -/

theorem ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful ciphersuite.hash_ref.HashReference
  ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserialize
  := by
  derive_de_std_lawful ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.Lawful
    [ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserialize.tls_deserialize]
    [ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize, ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful]

theorem ciphersuite.signature.Signature.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful ciphersuite.signature.Signature
  ciphersuite.signature.Signature.Insts.Tls_codecDeserialize
  := by
  derive_de_std_lawful ciphersuite.signature.Signature.Insts.Tls_codecSize.Lawful
    [ciphersuite.signature.Signature.Insts.Tls_codecDeserialize.tls_deserialize]
    [ciphersuite.signature.Signature.Insts.Tls_codecSize, ciphersuite.signature.Signature.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful]

theorem ciphersuite.signature.SignContent.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful ciphersuite.signature.SignContent
  ciphersuite.signature.SignContent.Insts.Tls_codecDeserialize
  := by
  derive_de_std_lawful ciphersuite.signature.SignContent.Insts.Tls_codecSize.Lawful
    [ciphersuite.signature.SignContent.Insts.Tls_codecDeserialize.tls_deserialize]
    [ciphersuite.signature.SignContent.Insts.Tls_codecSize, ciphersuite.signature.SignContent.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful]

theorem ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful ciphersuite.hpke.EncryptContext
  ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserialize
  := by
  derive_de_std_lawful ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize.Lawful
    [ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserialize.tls_deserialize]
    [ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize, ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful]

theorem ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful ciphersuite.reuse_guard.ReuseGuard
  ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserialize
  := by
  derive_de_std_lawful ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.Lawful
    [ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserialize.tls_deserialize]
    [ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize, ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.tls_serialized_len]
    [(tls_codec.ArrayU8LEN.Insts.Tls_codecDeserialize.Lawful 4#usize)]

theorem credentials.CredentialType.Insts.CoreFmtDebug.Lawful :
  core.fmt.Debug.Lawful credentials.CredentialType
  credentials.CredentialType.Insts.CoreFmtDebug
  :=
  ⟨⟩

theorem credentials.CredentialType.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful credentials.CredentialType
  credentials.CredentialType.Insts.Tls_codecSize
  :=
  by derive_size_lawful [credentials.CredentialType.Insts.Tls_codecSize.tls_serialized_len] []

theorem credentials.CredentialType.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful credentials.CredentialType
  credentials.CredentialType.Insts.Tls_codecDeserialize
  := by
  u16_read_de credentials.CredentialType.Insts.Tls_codecSize.Lawful,
    credentials.CredentialType.Insts.Tls_codecDeserialize.tls_deserialize,
    credentials.CredentialType.Insts.CoreConvertFromU16.from

theorem credentials.CredentialType.Insts.CoreCmpPartialEqCredentialType.Lawful
  :
  core.cmp.PartialEq.Lawful credentials.CredentialType
  credentials.CredentialType
  credentials.CredentialType.Insts.CoreCmpPartialEqCredentialType
  := by
  u16_enum_eq_lawful credentials.CredentialType.Insts.CoreCmpPartialEqCredentialType, credentials.CredentialType.Insts.CoreCmpPartialEqCredentialType.eq,
    credentials.CredentialType.read_discriminant

theorem credentials.CredentialType.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful credentials.CredentialType
  credentials.CredentialType.Insts.Tls_codecSerialize
  := by
  canon_u16_ser credentials.CredentialType.Insts.Tls_codecSize.Lawful, credentials.CredentialType.Insts.CoreCmpPartialEqCredentialType.Lawful,
    U16.Insts.CoreConvertFromCredentialType.from, credentials.CredentialType.Insts.CoreConvertFromU16.from, credentials.CredentialType.Insts.Tls_codecSerialize,
    credentials.CredentialType.Insts.Tls_codecSerialize.tls_serialize, credentials.CredentialType.Insts.CoreFmtDebug, credentials.CredentialType.Insts.CoreFmtDebug.fmt.ok_spec

theorem credentials.CredentialType.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful credentials.CredentialType
  credentials.CredentialType.Insts.Tls_codecDeserializeBytes
  := by
  debytes_via_reader credentials.CredentialType.Insts.Tls_codecDeserializeBytes,
    credentials.CredentialType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    credentials.CredentialType.Insts.Tls_codecDeserialize.Lawful,
    credentials.CredentialType.Insts.Tls_codecSize.Lawful
theorem credentials.Credential.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful credentials.Credential
  credentials.Credential.Insts.Tls_codecSize
  :=
  by derive_size_lawful [credentials.Credential.Insts.Tls_codecSize.tls_serialized_len] [credentials.CredentialType.Insts.Tls_codecSize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]

theorem credentials.Credential.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful credentials.Credential
  credentials.Credential.Insts.Tls_codecSerialize
  := by
  derive_ser_std_lawful credentials.Credential.Insts.Tls_codecSize.Lawful
    [credentials.Credential.Insts.Tls_codecSerialize.tls_serialize, Shared0Credential.Insts.Tls_codecSize.tls_serialized_len]
    [credentials.Credential.Insts.Tls_codecSize, credentials.Credential.Insts.Tls_codecSize.tls_serialized_len]
    [credentials.CredentialType.Insts.Tls_codecSerialize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful]

theorem credentials.Credential.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful credentials.Credential
  credentials.Credential.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful credentials.Credential.Insts.Tls_codecSize.Lawful [credentials.Credential.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, credentials.Credential.Insts.Tls_codecSize.tls_serialized_len] [credentials.CredentialType.Insts.Tls_codecDeserializeBytes.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.Lawful]

theorem
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.Lawful
  :
  tls_codec.Size.Lawful
  extensions.application_id_extension.ApplicationIdExtension
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize
  :=
  by derive_size_lawful [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]

theorem
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize.Lawful
  :
  tls_codec.Deserialize.Lawful
  extensions.application_id_extension.ApplicationIdExtension
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize
  := by
  refine de_lawful_of_runs _ extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.Lawful
    (P := fun _ _ _ => True) ?_ (fun _ _ => rfl)
  have hsize : ∀ u sz, quic_vec.VLBytes.Insts.Tls_codecSize.tls_serialized_len u = ok sz →
      extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.tls_serialized_len ⟨u⟩ = ok sz := by
    intro u sz hsz
    simp only [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.tls_serialized_len]
    rw [hsz]
    simp [len_add_ok, lenAdd_0]
  newtype_de quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful,
    extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize.tls_deserialize, hsize

theorem
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserializeBytes.Lawful
  :
  tls_codec.DeserializeBytes.Lawful
  extensions.application_id_extension.ApplicationIdExtension
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.Lawful [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.Lawful]

theorem messages.proposals.ProposalType.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful messages.proposals.ProposalType
  messages.proposals.ProposalType.Insts.Tls_codecSize
  :=
  by derive_size_lawful [messages.proposals.ProposalType.Insts.Tls_codecSize.tls_serialized_len] []

theorem extensions.ExtensionType.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.Tls_codecSize
  :=
  by derive_size_lawful [extensions.ExtensionType.Insts.Tls_codecSize.tls_serialized_len] []

theorem
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.Lawful
  :
  tls_codec.Size.Lawful extensions.external_sender_extension.ExternalSender
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize
  :=
  by derive_size_lawful [extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.tls_serialized_len] [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.Lawful, credentials.Credential.Insts.Tls_codecSize.Lawful]

theorem messages.proposals.ProposalType.Insts.CoreCmpPartialEqProposalType.Lawful
  :
  core.cmp.PartialEq.Lawful messages.proposals.ProposalType
  messages.proposals.ProposalType
  messages.proposals.ProposalType.Insts.CoreCmpPartialEqProposalType
  := by
  u16_enum_eq_lawful messages.proposals.ProposalType.Insts.CoreCmpPartialEqProposalType, messages.proposals.ProposalType.Insts.CoreCmpPartialEqProposalType.eq,
    messages.proposals.ProposalType.read_discriminant

theorem messages.proposals.ProposalType.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful messages.proposals.ProposalType
  messages.proposals.ProposalType.Insts.Tls_codecSerialize
  := by
  canon_u16_ser messages.proposals.ProposalType.Insts.Tls_codecSize.Lawful, messages.proposals.ProposalType.Insts.CoreCmpPartialEqProposalType.Lawful,
    U16.Insts.CoreConvertFromProposalType.from, messages.proposals.ProposalType.Insts.CoreConvertFromU16.from, messages.proposals.ProposalType.Insts.Tls_codecSerialize,
    messages.proposals.ProposalType.Insts.Tls_codecSerialize.tls_serialize, messages.proposals.ProposalType.Insts.CoreFmtDebug, messages.proposals.ProposalType.Insts.CoreFmtDebug.fmt.ok_spec

theorem messages.proposals.ProposalType.Insts.CoreFmtDebug.Lawful :
  core.fmt.Debug.Lawful messages.proposals.ProposalType
  messages.proposals.ProposalType.Insts.CoreFmtDebug
  :=
  ⟨⟩

theorem extensions.ExtensionType.Insts.CoreCmpPartialEqExtensionType.Lawful
  :
  core.cmp.PartialEq.Lawful extensions.ExtensionType
  extensions.ExtensionType
  extensions.ExtensionType.Insts.CoreCmpPartialEqExtensionType
  := by
  u16_enum_eq_lawful extensions.ExtensionType.Insts.CoreCmpPartialEqExtensionType, extensions.ExtensionType.Insts.CoreCmpPartialEqExtensionType.eq,
    extensions.ExtensionType.read_discriminant

theorem extensions.ExtensionType.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.Tls_codecSerialize
  := by
  canon_u16_ser extensions.ExtensionType.Insts.Tls_codecSize.Lawful, extensions.ExtensionType.Insts.CoreCmpPartialEqExtensionType.Lawful,
    U16.Insts.CoreConvertFromExtensionType.from, extensions.ExtensionType.Insts.CoreConvertFromU16.from, extensions.ExtensionType.Insts.Tls_codecSerialize,
    extensions.ExtensionType.Insts.Tls_codecSerialize.tls_serialize, extensions.ExtensionType.Insts.CoreFmtDebug, extensions.ExtensionType.Insts.CoreFmtDebug.fmt.ok_spec

theorem extensions.ExtensionType.Insts.CoreFmtDebug.Lawful :
  core.fmt.Debug.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.CoreFmtDebug
  :=
  ⟨⟩

theorem
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSerialize.Lawful
  :
  tls_codec.Serialize.Lawful
  extensions.external_sender_extension.ExternalSender
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSerialize
  := by
  derive_ser_std_lawful extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.Lawful
    [extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSerialize.tls_serialize, Shared0ExternalSender.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize, extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSerialize.Lawful, credentials.Credential.Insts.Tls_codecSerialize.Lawful]

theorem
  extensions.external_sender_extension.ExternalSender.Insts.CoreFmtDebug.Lawful
  :
  core.fmt.Debug.Lawful extensions.external_sender_extension.ExternalSender
  extensions.external_sender_extension.ExternalSender.Insts.CoreFmtDebug
  :=
  ⟨⟩

theorem
  extensions.codec.SerializeExtension.tls_serialize.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.Lawful
  {W : Type} (coreiowriteWriteInst : core.io.write.Write W)
  (coreiowriteWriteInstLawful : core.io.write.Write.Lawful W
  coreiowriteWriteInst) :
  core.ops.function.FnOnce.Lawful
  (extensions.codec.SerializeExtension.tls_serialize.closure_2 W) Std.Usize
  Std.Usize
  (extensions.codec.SerializeExtension.tls_serialize.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize
  coreiowriteWriteInst)
  :=
  ⟨⟩

theorem
  extensions.codec.SerializeExtension.tls_serialize.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.Lawful
  {W : Type} (coreiowriteWriteInst : core.io.write.Write W)
  (coreiowriteWriteInstLawful : core.io.write.Write.Lawful W
  coreiowriteWriteInst) :
  core.ops.function.FnOnce.Lawful
  (extensions.codec.SerializeExtension.tls_serialize.closure_1 W)
  core.io.error.Error tls_codec.Error
  (extensions.codec.SerializeExtension.tls_serialize.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
  coreiowriteWriteInst)
  :=
  ⟨⟩

theorem
  extensions.codec.SerializeExtension.tls_serialize.closure.Insts.CoreOpsFunctionFnOnceTupleTupleUsize.Lawful
  {W : Type} (coreiowriteWriteInst : core.io.write.Write W)
  (coreiowriteWriteInstLawful : core.io.write.Write.Lawful W
  coreiowriteWriteInst) :
  core.ops.function.FnOnce.Lawful
  (extensions.codec.SerializeExtension.tls_serialize.closure W) Unit Std.Usize
  (extensions.codec.SerializeExtension.tls_serialize.closure.Insts.CoreOpsFunctionFnOnceTupleTupleUsize
  coreiowriteWriteInst)
  :=
  ⟨⟩

theorem
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.Lawful
  :
  tls_codec.Size.Lawful
  extensions.required_capabilities.RequiredCapabilitiesExtension
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize
  :=
  by derive_size_lawful [extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.tls_serialized_len] [(tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ extensions.ExtensionType.Insts.Tls_codecSize.Lawful), (tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ messages.proposals.ProposalType.Insts.Tls_codecSize.Lawful), (tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ credentials.CredentialType.Insts.Tls_codecSize.Lawful)]

theorem messages.proposals.ProposalType.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful messages.proposals.ProposalType
  messages.proposals.ProposalType.Insts.Tls_codecDeserialize
  := by
  u16_read_de messages.proposals.ProposalType.Insts.Tls_codecSize.Lawful,
    messages.proposals.ProposalType.Insts.Tls_codecDeserialize.tls_deserialize,
    messages.proposals.ProposalType.Insts.CoreConvertFromU16.from

theorem extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.Tls_codecDeserialize
  := by
  u16_read_de extensions.ExtensionType.Insts.Tls_codecSize.Lawful,
    extensions.ExtensionType.Insts.Tls_codecDeserialize.tls_deserialize,
    extensions.ExtensionType.Insts.CoreConvertFromU16.from

theorem
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize.Lawful
  :
  tls_codec.Deserialize.Lawful
  extensions.required_capabilities.RequiredCapabilitiesExtension
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize
  := by
  derive_de_std_lawful extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.Lawful
    [extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize.tls_deserialize]
    [extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize, extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.tls_serialized_len]
    [(tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize.Lawful _ extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful), (tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize.Lawful _ messages.proposals.ProposalType.Insts.Tls_codecDeserialize.Lawful), (tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize.Lawful _ credentials.CredentialType.Insts.Tls_codecDeserialize.Lawful)]

theorem
  extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize.Lawful
  :
  tls_codec.Size.Lawful extensions.ratchet_tree_extension.RatchetTreeExtension
  extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize
  :=
  -- ASSUMED: `Assumptions/RatchetTreeSpecs.lean`
  extensions.ratchet_tree_extension.RatchetTreeExtension.size_lawful_assumed

theorem
  extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecDeserialize.Lawful
  :
  tls_codec.Deserialize.Lawful
  extensions.ratchet_tree_extension.RatchetTreeExtension
  extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecDeserialize
  :=
  -- ASSUMED: `Assumptions/RatchetTreeSpecs.lean`
  extensions.ratchet_tree_extension.RatchetTreeExtension.deserialize_lawful_assumed

theorem extensions.last_resort.LastResortExtension.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful extensions.last_resort.LastResortExtension
  extensions.last_resort.LastResortExtension.Insts.Tls_codecSize
  :=
  by derive_size_lawful [extensions.last_resort.LastResortExtension.Insts.Tls_codecSize.tls_serialized_len] []

theorem
  extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserialize.Lawful
  :
  tls_codec.Deserialize.Lawful extensions.last_resort.LastResortExtension
  extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserialize
  := by
  refine de_lawful_of_runs _ extensions.last_resort.LastResortExtension.Insts.Tls_codecSize.Lawful
    (P := fun _ _ _ => True) ?_ (fun _ _ => rfl)
  intro R RI v a law r
  refine ok_triple_of fun val _ => ⟨0, 0#usize, by omega, (law.adv_zero r).symm, rfl, rfl, trivial⟩

theorem ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful ciphersuite.signature.SignaturePublicKey
  ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserialize
  := by
  derive_de_std_lawful ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.Lawful
    [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserialize.tls_deserialize]
    [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize,
      ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful]

theorem credentials.Credential.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful credentials.Credential
  credentials.Credential.Insts.Tls_codecDeserialize
  := by
  derive_de_std_lawful credentials.Credential.Insts.Tls_codecSize.Lawful
    [credentials.Credential.Insts.Tls_codecDeserialize.tls_deserialize]
    [credentials.Credential.Insts.Tls_codecSize, credentials.Credential.Insts.Tls_codecSize.tls_serialized_len]
    [credentials.CredentialType.Insts.Tls_codecDeserialize.Lawful,
      tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful]

theorem
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize.Lawful
  :
  tls_codec.Deserialize.Lawful
  extensions.external_sender_extension.ExternalSender
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize
  := by
  derive_de_std_lawful extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.Lawful
    [extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize.tls_deserialize]
    [extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize, extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserialize.Lawful, credentials.Credential.Insts.Tls_codecDeserialize.Lawful]

theorem
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.Lawful
  :
  tls_codec.Size.Lawful extensions.external_pub_extension.ExternalPubExtension
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize
  :=
  by derive_size_lawful [extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]

theorem
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize.Lawful
  :
  tls_codec.Deserialize.Lawful
  extensions.external_pub_extension.ExternalPubExtension
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize
  := by
  refine de_lawful_of_runs _ extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.Lawful
    (P := fun _ _ _ => True) ?_ (fun _ _ => rfl)
  have hsize : ∀ u sz, quic_vec.VLBytes.Insts.Tls_codecSize.tls_serialized_len u = ok sz →
      extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.tls_serialized_len ⟨u⟩ = ok sz := by
    intro u sz hsz
    simp only [extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.tls_serialized_len]
    rw [hsz]
    simp [len_add_ok, lenAdd_0]
  newtype_de quic_vec.VLBytes.Insts.Tls_codecDeserialize.Lawful,
    extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize.tls_deserialize, hsize

theorem
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserializeBytes.Lawful
  :
  tls_codec.DeserializeBytes.Lawful
  extensions.external_pub_extension.ExternalPubExtension
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.Lawful [extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.quic_vec.VLBytes.Insts.Tls_codecDeserializeBytes.Lawful]

theorem
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserializeBytes.Lawful
  :
  tls_codec.DeserializeBytes.Lawful
  extensions.external_sender_extension.ExternalSender
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.Lawful [extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.tls_serialized_len] [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserializeBytes.Lawful, credentials.Credential.Insts.Tls_codecDeserializeBytes.Lawful]

theorem
  extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserializeBytes.Lawful
  :
  tls_codec.DeserializeBytes.Lawful extensions.last_resort.LastResortExtension
  extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful extensions.last_resort.LastResortExtension.Insts.Tls_codecSize.Lawful [extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, extensions.last_resort.LastResortExtension.Insts.Tls_codecSize.tls_serialized_len] []

theorem extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.Tls_codecDeserializeBytes
  := by
  debytes_via_reader extensions.ExtensionType.Insts.Tls_codecDeserializeBytes,
    extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful, extensions.ExtensionType.Insts.Tls_codecSize.Lawful

theorem extensions.Extension.Insts.CoreFmtDebug.Lawful :
  core.fmt.Debug.Lawful extensions.Extension
  extensions.Extension.Insts.CoreFmtDebug
  :=
  ⟨⟩

/-- `Extension`'s `Size` is total given its payloads' (the `RatchetTreeExtension` one is a
parameter: its impl is opaque). -/
private theorem extensions.Extension.size_lawful_of
    (hRT : tls_codec.Size.Lawful extensions.ratchet_tree_extension.RatchetTreeExtension
      extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize) :
    tls_codec.Size.Lawful extensions.Extension extensions.Extension.Insts.Tls_codecSize := by
  derive_size_lawful [extensions.Extension.Insts.Tls_codecSize.tls_serialized_len, extensions.codec.vlbytes_len_len] [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.Lawful, hRT, extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.Lawful, extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.Lawful, (tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.Lawful), extensions.last_resort.LastResortExtension.Insts.Tls_codecSize.Lawful]

theorem extensions.Extension.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful extensions.Extension
  extensions.Extension.Insts.Tls_codecSize
  :=
  extensions.Extension.size_lawful_of
    extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize.Lawful

theorem extensions.Extensions.Insts.Tls_codecSize.Lawful (T : Type) :
  tls_codec.Size.Lawful (extensions.Extensions T)
  (extensions.Extensions.Insts.Tls_codecSize T)
  := by
  derive_size_lawful [extensions.Extensions.Insts.Tls_codecSize.tls_serialized_len] [(tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ extensions.Extension.Insts.Tls_codecSize.Lawful)]

theorem
  extensions.DeserializeExtensions.tls_deserialize.closure.Insts.CoreOpsFunctionFnOnceTupleInvalidExtensionErrorError.Lawful
  {T : Type} {R : Type} {Clause0_Error : Type} (ExtensionValidatorInst :
  extensions.ExtensionValidator T Clause0_Error) (allocstringToStringInst :
  alloc.string.ToString Clause0_Error)
  (coreconvertFromInvalidExtensionErrorClause0_ErrorInst : core.convert.From
  extensions.errors.InvalidExtensionError Clause0_Error) (allocioreadReadInst :
  alloc.io.read.Read R)
  (ExtensionValidatorInstLawful : extensions.ExtensionValidator.Lawful T
  Clause0_Error ExtensionValidatorInst)
  (allocstringToStringInstLawful : alloc.string.ToString.Lawful Clause0_Error
  allocstringToStringInst)
  (coreconvertFromInvalidExtensionErrorClause0_ErrorInstLawful :
  core.convert.From.Lawful extensions.errors.InvalidExtensionError
  Clause0_Error coreconvertFromInvalidExtensionErrorClause0_ErrorInst)
  (allocioreadReadInstLawful : alloc.io.read.Read.Lawful R allocioreadReadInst)
  :
  core.ops.function.FnOnce.Lawful
  (extensions.DeserializeExtensions.tls_deserialize.closure T R Clause0_Error)
  extensions.errors.InvalidExtensionError tls_codec.Error
  (extensions.DeserializeExtensions.tls_deserialize.closure.Insts.CoreOpsFunctionFnOnceTupleInvalidExtensionErrorError
  ExtensionValidatorInst allocstringToStringInst
  coreconvertFromInvalidExtensionErrorClause0_ErrorInst allocioreadReadInst)
  :=
  ⟨⟩

/-! ## The extension validators: `validate_extension_type` returns. -/

theorem
  extensions.AnyObject.Insts.OpenmlsExtensionsExtensionValidatorInfallible.Lawful
  :
  extensions.ExtensionValidator.Lawful extensions.AnyObject
  core.convert.Infallible
  extensions.AnyObject.Insts.OpenmlsExtensionsExtensionValidatorInfallible
  := by
  refine ⟨⟨⟩, ?_⟩
  intro ext _
  mvcgen [extensions.AnyObject.Insts.OpenmlsExtensionsExtensionValidatorInfallible.validate_extension_type]

theorem
  messages.group_info.GroupInfo.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInGroupInfoError.Lawful
  :
  extensions.ExtensionValidator.Lawful messages.group_info.GroupInfo
  extensions.errors.ExtensionTypeNotValidInGroupInfoError
  messages.group_info.GroupInfo.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInGroupInfoError
  := by
  refine ⟨⟨⟩, ?_⟩
  intro ext _
  cases ext <;> mvcgen [messages.group_info.GroupInfo.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInGroupInfoError.validate_extension_type,
    extensions.Extension.extension_type, extensions.ExtensionType.is_valid_in_group_info]

theorem
  group.group_context.GroupContext.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInGroupContextError.Lawful
  :
  extensions.ExtensionValidator.Lawful group.group_context.GroupContext
  extensions.errors.ExtensionTypeNotValidInGroupContextError
  group.group_context.GroupContext.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInGroupContextError
  := by
  refine ⟨⟨⟩, ?_⟩
  intro ext _
  cases ext <;> mvcgen [group.group_context.GroupContext.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInGroupContextError.validate_extension_type,
    extensions.Extension.extension_type, extensions.ExtensionType.is_valid_in_group_context]

theorem
  key_packages.KeyPackage.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInKeyPackageError.Lawful
  :
  extensions.ExtensionValidator.Lawful key_packages.KeyPackage
  extensions.errors.ExtensionTypeNotValidInKeyPackageError
  key_packages.KeyPackage.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInKeyPackageError
  := by
  refine ⟨⟨⟩, ?_⟩
  intro ext _
  cases ext <;> mvcgen [key_packages.KeyPackage.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInKeyPackageError.validate_extension_type,
    extensions.Extension.extension_type, extensions.ExtensionType.is_valid_in_key_package]

theorem
  treesync.node.leaf_node.LeafNode.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInLeafNodeError.Lawful
  :
  extensions.ExtensionValidator.Lawful treesync.node.leaf_node.LeafNode
  extensions.errors.ExtensionTypeNotValidInLeafNodeError
  treesync.node.leaf_node.LeafNode.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInLeafNodeError
  := by
  refine ⟨⟨⟩, ?_⟩
  intro ext _
  cases ext <;> mvcgen [treesync.node.leaf_node.LeafNode.Insts.OpenmlsExtensionsExtensionValidatorExtensionTypeNotValidInLeafNodeError.validate_extension_type,
    extensions.Extension.extension_type, extensions.ExtensionType.is_valid_in_leaf_node]

theorem messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.Lawful
  :
  tls_codec.DeserializeBytes.Lawful messages.proposals.ProposalType
  messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes
  := by
  debytes_via_reader messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes,
    messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    messages.proposals.ProposalType.Insts.Tls_codecDeserialize.Lawful, messages.proposals.ProposalType.Insts.Tls_codecSize.Lawful

theorem
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserializeBytes.Lawful
  :
  tls_codec.DeserializeBytes.Lawful
  extensions.required_capabilities.RequiredCapabilitiesExtension
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.Lawful [extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.tls_serialized_len] [tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.Lawful _ extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.Lawful, tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.Lawful _ messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.Lawful, tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserializeBytes.Lawful _ credentials.CredentialType.Insts.Tls_codecDeserializeBytes.Lawful]

theorem P.Insts.CoreOpsFunctionFnOnceTupleU16ProtocolVersion.Lawful :
  core.ops.function.FnOnce.Lawful (Std.U16 → RustM versions.ProtocolVersion)
  Std.U16 versions.ProtocolVersion
  P.Insts.CoreOpsFunctionFnOnceTupleU16ProtocolVersion
  :=
  ⟨⟩

theorem versions.ProtocolVersion.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful versions.ProtocolVersion
  versions.ProtocolVersion.Insts.Tls_codecSize
  :=
  by derive_size_lawful [versions.ProtocolVersion.Insts.Tls_codecSize.tls_serialized_len] []

theorem versions.ProtocolVersion.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful versions.ProtocolVersion
  versions.ProtocolVersion.Insts.Tls_codecSerialize
  := by
  -- `Other(1)` is rejected (it would decode as `Mls10`, upstream 2026-08): no encoding
  refine ser_lawful_of_runs _ versions.ProtocolVersion.Insts.Tls_codecSize.Lawful
    (fun x => match x with
      | .Mls10 => some (Aeneas.Std.core.num.U16.to_be_bytes 1#u16).val
      | .Other v => if v = 1#u16 then none else some (Aeneas.Std.core.num.U16.to_be_bytes v).val)
    (fun x => ⟨2#usize, rfl, ?_, ?_⟩) (fun _ => rfl)
  · intro _ b hb
    cases x with
    | Mls10 => cases hb; simp
    | Other v =>
      by_cases hv : v = 1#u16 <;> simp only [hv, if_true, if_false, reduceCtorEq] at hb
      cases hb; simp
  · intro W WI hWI w hroom
    cases x with
    | Mls10 => exact U16.ser_runs 1#u16 W WI hWI w hroom
    | Other v =>
      by_cases hv : v = 1#u16
      · subst hv
        refine ⟨_, w, rfl, fun b hb => by simp at hb, fun _ => ⟨_, rfl⟩⟩
      · simp only [hv, if_false]
        have h := U16.ser_runs v W WI hWI w hroom
        simp only [versions.ProtocolVersion.Insts.Tls_codecSerialize,
          versions.ProtocolVersion.Insts.Tls_codecSerialize.tls_serialize]
        split
        · exfalso; exact hv rfl
        · exact h

theorem versions.ProtocolVersion.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful versions.ProtocolVersion
  versions.ProtocolVersion.Insts.Tls_codecDeserialize
  := by
  refine de_lawful_of_runs _ versions.ProtocolVersion.Insts.Tls_codecSize.Lawful
    (P := fun _ _ _ => True) ?_ (fun _ _ => rfl)
  intro R RI v a law r
  obtain ⟨⟨res, r'⟩, hr, hp⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (U16.de_runs R RI v a law r)
  have hf : ∀ u, ∃ y, versions.ProtocolVersion.Insts.CoreConvertFromU16.from u = ok y := by
    intro u; unfold versions.ProtocolVersion.Insts.CoreConvertFromU16.from; split <;> exact ⟨_, rfl⟩
  simp only [versions.ProtocolVersion.Insts.Tls_codecDeserialize,
    versions.ProtocolVersion.Insts.Tls_codecDeserialize.tls_deserialize]
  rw [show tls_codec.U16.Insts.Tls_codecDeserialize.tls_deserialize RI r = ok (res, r') from hr]
  cases res with
  | Err e =>
    simp only [bind_tc_ok, core.result.Result.map]
    mvcgen
    intro val h; cases h
  | Ok u =>
    obtain ⟨y, hy⟩ := hf u
    obtain ⟨n, sz, hn, h2, hsz, hszn, -⟩ := hp u rfl
    have h2' : sz = 2#usize := by
      have := hsz.symm.trans (u16_size u); cases this; rfl
    subst h2'
    simp only [bind_tc_ok, core.result.Result.map,
      P.Insts.CoreOpsFunctionFnOnceTupleU16ProtocolVersion,
      P.Insts.CoreOpsFunctionFnOnceTupleU16ProtocolVersion.call_once, hy]
    mvcgen [hy]
    intro val h; cases h; exact ⟨n, 2#usize, hn, h2, rfl, hszn⟩

theorem versions.ProtocolVersion.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful versions.ProtocolVersion
  versions.ProtocolVersion.Insts.Tls_codecDeserializeBytes
  :=
  by derive_deser_lawful versions.ProtocolVersion.Insts.Tls_codecSize.Lawful [versions.ProtocolVersion.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, versions.ProtocolVersion.Insts.Tls_codecSize.tls_serialized_len, versions.ProtocolVersion.Insts.CoreConvertFromU16.from] [tls_codec.U16.Insts.Tls_codecDeserializeBytes.Lawful]

/-! ## `Extension` / `Extensions<T>` `std` codecs (hand-written, `extensions/codec.rs`; true since
the `vlbytes_len_len` fix, upstream #2147). The proofs are in `Verification/ExtensionStd.lean` / `ExtensionStdSer.lean`, from the
payloads' `Lawful`s (the payload serializers' generated obligations below). -/

theorem extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize.Lawful
  :
  tls_codec.Serialize.Lawful
  extensions.application_id_extension.ApplicationIdExtension
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize
  := by
  derive_ser_std_lawful extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.Lawful
    [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize.tls_serialize, Shared0ApplicationIdExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize, extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful]

theorem extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize.Lawful
  :
  tls_codec.Serialize.Lawful
  extensions.external_pub_extension.ExternalPubExtension
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize
  := by
  derive_ser_std_lawful extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.Lawful
    [extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize.tls_serialize, Shared0ExternalPubExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize, extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.tls_serialized_len]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSerialize.Lawful]

theorem extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize.Lawful
  :
  tls_codec.Serialize.Lawful
  extensions.required_capabilities.RequiredCapabilitiesExtension
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize
  := by
  derive_ser_std_lawful extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.Lawful
    [extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize.tls_serialize, Shared0RequiredCapabilitiesExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize, extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.tls_serialized_len]
    [(tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize.Lawful _ _
        extensions.ExtensionType.Insts.Tls_codecSerialize.Lawful extensions.ExtensionType.Insts.CoreFmtDebug.Lawful),
      (tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize.Lawful _ _
        messages.proposals.ProposalType.Insts.Tls_codecSerialize.Lawful messages.proposals.ProposalType.Insts.CoreFmtDebug.Lawful),
      (tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize.Lawful _ _
        credentials.CredentialType.Insts.Tls_codecSerialize.Lawful credentials.CredentialType.Insts.CoreFmtDebug.Lawful)]

theorem extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful extensions.last_resort.LastResortExtension
  extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize
  := by
  -- no field: writes nothing
  refine ser_lawful_of_some _ extensions.last_resort.LastResortExtension.Insts.Tls_codecSize.Lawful
    (fun x => ⟨0#usize, [], rfl, by have := imax_ge; simp, rfl, ?_⟩) (fun _ => rfl)
  intro W WI hWI w _
  refine ⟨.Ok 0#usize, w, ?_, fun b hb => ?_, fun h => by cases h⟩
  · simp [extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize, extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize.tls_serialize,
      Shared0LastResortExtension.Insts.Tls_codecSize.tls_serialized_len,
      extensions.last_resort.LastResortExtension.Insts.Tls_codecSize.tls_serialized_len]
  · cases hb; exact ⟨⟨0#usize, rfl, rfl⟩, by simp⟩

theorem extensions.Extension.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful extensions.Extension
  extensions.Extension.Insts.Tls_codecSerialize
  :=
  extensions.Extension.ser_lawful_of extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize.Lawful
    -- ASSUMED: `Assumptions/RatchetTreeSpecs.lean`
    extensions.ratchet_tree_extension.RatchetTreeExtension.serialize_lawful_assumed
    extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize.Lawful extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize.Lawful
    (tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize.Lawful _ _
      extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSerialize.Lawful extensions.external_sender_extension.ExternalSender.Insts.CoreFmtDebug.Lawful)
    extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize.Lawful extensions.Extension.Insts.Tls_codecSize.Lawful
    extensions.ExtensionType.Insts.Tls_codecSerialize.Lawful

theorem extensions.Extension.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful extensions.Extension
  extensions.Extension.Insts.Tls_codecDeserialize
  :=
  extensions.Extension.de_lawful_of extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful
    extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize.Lawful extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize.Lawful
    (tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize.Lawful _
      extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize.Lawful)
    extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserialize.Lawful extensions.Extension.Insts.Tls_codecSize.Lawful

theorem extensions.Extension.Insts.Tls_codecDeserializeBytes.Lawful :
  tls_codec.DeserializeBytes.Lawful extensions.Extension
  extensions.Extension.Insts.Tls_codecDeserializeBytes
  := by
  debytes_via_reader extensions.Extension.Insts.Tls_codecDeserializeBytes,
    extensions.Extension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes,
    extensions.Extension.Insts.Tls_codecDeserialize.Lawful,
    extensions.Extension.Insts.Tls_codecSize.Lawful

theorem extensions.Extensions.Insts.Tls_codecSerialize.Lawful (T : Type) :
  tls_codec.Serialize.Lawful (extensions.Extensions T)
  (extensions.Extensions.Insts.Tls_codecSerialize T)
  := by
  have hV := tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize.Lawful _ _
    extensions.Extension.Insts.Tls_codecSerialize.Lawful extensions.Extension.Insts.CoreFmtDebug.Lawful
  refine ser_lawful_of_runs _ (extensions.Extensions.Insts.Tls_codecSize.Lawful T)
    (fun x => encOut (tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize
      extensions.Extension.Insts.Tls_codecSerialize extensions.Extension.Insts.CoreFmtDebug) x.unique)
    (fun x => ⟨_, size_ok hV.SizeInstLawful x.unique,
      fun hle b hb => hV.enc_len x.unique _ (size_ok hV.SizeInstLawful x.unique) hle b hb,
      hV.runs x.unique _ (size_ok hV.SizeInstLawful x.unique)⟩) (fun _ => rfl)

theorem extensions.Extensions.Insts.Tls_codecDeserialize.Lawful {T : Type}
  {Clause0_Error : Type} (ExtensionValidatorInst :
  extensions.ExtensionValidator T Clause0_Error) (allocstringToStringInst :
  alloc.string.ToString Clause0_Error)
  (coreconvertFromInvalidExtensionErrorClause0_ErrorInst : core.convert.From
  extensions.errors.InvalidExtensionError Clause0_Error)
  (ExtensionValidatorInstLawful : extensions.ExtensionValidator.Lawful T
  Clause0_Error ExtensionValidatorInst)
  (allocstringToStringInstLawful : alloc.string.ToString.Lawful Clause0_Error
  allocstringToStringInst)
  (coreconvertFromInvalidExtensionErrorClause0_ErrorInstLawful :
  core.convert.From.Lawful extensions.errors.InvalidExtensionError
  Clause0_Error coreconvertFromInvalidExtensionErrorClause0_ErrorInst) :
  tls_codec.Deserialize.Lawful (extensions.Extensions T)
  (extensions.Extensions.Insts.Tls_codecDeserialize ExtensionValidatorInst
  allocstringToStringInst
  coreconvertFromInvalidExtensionErrorClause0_ErrorInst)
  := by
  -- total by `ExtensionValidator.Lawful` / `ToString.Lawful`; proofs in
  -- `Verification/ExtensionsTryFrom.lean`
  exact extensions.Extensions.de_lawful_of ExtensionValidatorInst allocstringToStringInst
    coreconvertFromInvalidExtensionErrorClause0_ErrorInst
    (extensions.Extensions.Insts.Tls_codecSize.Lawful T) extensions.Extension.Insts.Tls_codecSize.Lawful
    (extensions.extension_in.ExtensionIn.de_lawful_of
      extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful
      extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize.Lawful
      extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecDeserialize.Lawful
      extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize.Lawful
      extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize.Lawful
      (tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize.Lawful _
        extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize.Lawful)
      extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserialize.Lawful
      ExtensionValidatorInst allocstringToStringInst ExtensionValidatorInstLawful
      allocstringToStringInstLawful extensions.Extension.Insts.Tls_codecSize.Lawful)

theorem extensions.Extensions.Insts.Tls_codecDeserializeBytes.Lawful {T : Type}
  {Clause0_Error : Type} (ExtensionValidatorInst :
  extensions.ExtensionValidator T Clause0_Error) (allocstringToStringInst :
  alloc.string.ToString Clause0_Error)
  (coreconvertFromInvalidExtensionErrorClause0_ErrorInst : core.convert.From
  extensions.errors.InvalidExtensionError Clause0_Error)
  (ExtensionValidatorInstLawful : extensions.ExtensionValidator.Lawful T
  Clause0_Error ExtensionValidatorInst)
  (allocstringToStringInstLawful : alloc.string.ToString.Lawful Clause0_Error
  allocstringToStringInst)
  (coreconvertFromInvalidExtensionErrorClause0_ErrorInstLawful :
  core.convert.From.Lawful extensions.errors.InvalidExtensionError
  Clause0_Error coreconvertFromInvalidExtensionErrorClause0_ErrorInst) :
  tls_codec.DeserializeBytes.Lawful (extensions.Extensions T)
  (extensions.Extensions.Insts.Tls_codecDeserializeBytes ExtensionValidatorInst
  allocstringToStringInst
  coreconvertFromInvalidExtensionErrorClause0_ErrorInst)
  := by
  -- the reader left after the `std` deserializer (`debytes_via_reader`, inlined since the bytes
  -- deserializer takes the instances as arguments)
  have hDe := extensions.Extensions.Insts.Tls_codecDeserialize.Lawful ExtensionValidatorInst
    allocstringToStringInst coreconvertFromInvalidExtensionErrorClause0_ErrorInst
    ExtensionValidatorInstLawful allocstringToStringInstLawful
    coreconvertFromInvalidExtensionErrorClause0_ErrorInstLawful
  have hd : ∀ bytes, ⦃ ⌜ True ⌝ ⦄
      extensions.Extensions.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes ExtensionValidatorInst
        allocstringToStringInst coreconvertFromInvalidExtensionErrorClause0_ErrorInst bytes
      ⦃ ⇓ r => ⌜ (DeserializeBytes.tls_deserialize_bytes.post
        (extensions.Extensions.Insts.Tls_codecDeserializeBytes ExtensionValidatorInst
          allocstringToStringInst coreconvertFromInvalidExtensionErrorClause0_ErrorInst).SizeInst
        (extensions.Extensions.Insts.Tls_codecDeserializeBytes ExtensionValidatorInst
          allocstringToStringInst coreconvertFromInvalidExtensionErrorClause0_ErrorInst) bytes r).holds ⌝ ⦄ := by
    intro bytes
    have hT := hDe.runs _ _ _ _ StdIo.slice_law bytes
    mvcgen [extensions.Extensions.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes, hT]
    · rename_i p _ u _ hcf hp
      obtain ⟨n, sz, hn, h2, hsz, hszn⟩ := hp u (continue_eq_tryCF.mp hcf)
      rw [h2]
      exact debytes_reader_post_ok _ _ bytes u n sz hn hsz hszn
    · rename_i q _ _ _ _
      intro hbr
      refine try_break_vc (x := q.1) (fun e he => ?_) hbr
      mvcgen
      intro _
      exact DeserializeBytes.post_err _ _ _ _
  exact ⟨extensions.Extensions.Insts.Tls_codecSize.Lawful T, fun b _ => hd b,
    fun b _ => exact_bytes_spec (extensions.Extensions.Insts.Tls_codecDeserializeBytes ExtensionValidatorInst
      allocstringToStringInst coreconvertFromInvalidExtensionErrorClause0_ErrorInst) hd b⟩

/-! ## Obligations new with upstream 2026-08 (`ExtensionIn<T>`, sealed validators, `ExtensionType`
`Hash` / `Eq`) -/

theorem P.Insts.CoreOpsFunctionFnOnceTupleExtensionInExtension.Lawful {T :
  Type} {Clause0_Error : Type} (ExtensionValidatorInst :
  extensions.ExtensionValidator T Clause0_Error)
  (ExtensionValidatorInstLawful : extensions.ExtensionValidator.Lawful T
  Clause0_Error ExtensionValidatorInst) :
  core.ops.function.FnOnce.Lawful (extensions.extension_in.ExtensionIn T →
  RustM extensions.Extension) (extensions.extension_in.ExtensionIn T)
  extensions.Extension (P.Insts.CoreOpsFunctionFnOnceTupleExtensionInExtension
  ExtensionValidatorInst)
  :=
  ⟨⟩

theorem P.Insts.CoreOpsFunctionFnMutTupleExtensionInExtension.Lawful {T : Type}
  {Clause0_Error : Type} (ExtensionValidatorInst :
  extensions.ExtensionValidator T Clause0_Error)
  (ExtensionValidatorInstLawful : extensions.ExtensionValidator.Lawful T
  Clause0_Error ExtensionValidatorInst) :
  core.ops.function.FnMut.Lawful (extensions.extension_in.ExtensionIn T →
  RustM extensions.Extension) (extensions.extension_in.ExtensionIn T)
  extensions.Extension (P.Insts.CoreOpsFunctionFnMutTupleExtensionInExtension
  ExtensionValidatorInst)
  :=
  ⟨⟩

theorem extensions.ExtensionType.Insts.CoreHashHash.Lawful :
  core.hash.Hash.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.CoreHashHash
  :=
  ⟨⟩

theorem extensions.ExtensionType.Insts.CoreCmpEq.Lawful :
  core.cmp.Eq.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.CoreCmpEq
  := by
  constructor
  intro x y
  have h := extensions.ExtensionType.Insts.CoreCmpPartialEqExtensionType.Lawful.eq_spec x y
  simpa only [heq_iff_eq] using h

theorem extensions.extension_in.ExtensionIn.Insts.Tls_codecSize.Lawful {T :
  Type} {Clause0_Error : Type} (ExtensionValidatorInst :
  extensions.ExtensionValidator T Clause0_Error)
  (ExtensionValidatorInstLawful : extensions.ExtensionValidator.Lawful T
  Clause0_Error ExtensionValidatorInst) :
  tls_codec.Size.Lawful (extensions.extension_in.ExtensionIn T)
  (extensions.extension_in.ExtensionIn.Insts.Tls_codecSize
  ExtensionValidatorInst)
  :=
  extensions.extension_in.ExtensionIn.size_lawful ExtensionValidatorInst
    extensions.Extension.Insts.Tls_codecSize.Lawful

theorem
  extensions.extension_in.DeserializeExtensionIn.tls_deserialize.closure.Insts.CoreOpsFunctionFnOnceTupleClause0_ErrorError.Lawful
  {T : Type} {R : Type} {Clause0_Error : Type} (ExtensionValidatorInst :
  extensions.ExtensionValidator T Clause0_Error) (allocstringToStringInst :
  alloc.string.ToString Clause0_Error) (allocioreadReadInst :
  alloc.io.read.Read R)
  (ExtensionValidatorInstLawful : extensions.ExtensionValidator.Lawful T
  Clause0_Error ExtensionValidatorInst)
  (allocstringToStringInstLawful : alloc.string.ToString.Lawful Clause0_Error
  allocstringToStringInst)
  (allocioreadReadInstLawful : alloc.io.read.Read.Lawful R allocioreadReadInst)
  :
  core.ops.function.FnOnce.Lawful
  (extensions.extension_in.DeserializeExtensionIn.tls_deserialize.closure T R
  Clause0_Error) Clause0_Error tls_codec.Error
  (extensions.extension_in.DeserializeExtensionIn.tls_deserialize.closure.Insts.CoreOpsFunctionFnOnceTupleClause0_ErrorError
  ExtensionValidatorInst allocstringToStringInst allocioreadReadInst)
  :=
  ⟨⟩

theorem extensions.extension_in.ExtensionIn.Insts.Tls_codecDeserialize.Lawful
  {T : Type} {Clause0_Error : Type} (ExtensionValidatorInst :
  extensions.ExtensionValidator T Clause0_Error) (allocstringToStringInst :
  alloc.string.ToString Clause0_Error)
  (ExtensionValidatorInstLawful : extensions.ExtensionValidator.Lawful T
  Clause0_Error ExtensionValidatorInst)
  (allocstringToStringInstLawful : alloc.string.ToString.Lawful Clause0_Error
  allocstringToStringInst) :
  tls_codec.Deserialize.Lawful (extensions.extension_in.ExtensionIn T)
  (extensions.extension_in.ExtensionIn.Insts.Tls_codecDeserialize
  ExtensionValidatorInst allocstringToStringInst)
  :=
  extensions.extension_in.ExtensionIn.de_lawful_of
    extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful
    extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize.Lawful
    (tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize.Lawful _
      extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize.Lawful)
    extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserialize.Lawful
    ExtensionValidatorInst allocstringToStringInst ExtensionValidatorInstLawful
    allocstringToStringInstLawful extensions.Extension.Insts.Tls_codecSize.Lawful

theorem extensions.AnyObject.Insts.OpenmlsExtensionsPrivateSealed.Lawful :
  extensions.private.Sealed.Lawful extensions.AnyObject
  extensions.AnyObject.Insts.OpenmlsExtensionsPrivateSealed
  :=
  ⟨⟩

theorem
  messages.group_info.GroupInfo.Insts.OpenmlsExtensionsPrivateSealed.Lawful :
  extensions.private.Sealed.Lawful messages.group_info.GroupInfo
  messages.group_info.GroupInfo.Insts.OpenmlsExtensionsPrivateSealed
  :=
  ⟨⟩

theorem
  group.group_context.GroupContext.Insts.OpenmlsExtensionsPrivateSealed.Lawful
  :
  extensions.private.Sealed.Lawful group.group_context.GroupContext
  group.group_context.GroupContext.Insts.OpenmlsExtensionsPrivateSealed
  :=
  ⟨⟩

theorem key_packages.KeyPackage.Insts.OpenmlsExtensionsPrivateSealed.Lawful :
  extensions.private.Sealed.Lawful key_packages.KeyPackage
  key_packages.KeyPackage.Insts.OpenmlsExtensionsPrivateSealed
  :=
  ⟨⟩

theorem
  treesync.node.leaf_node.LeafNode.Insts.OpenmlsExtensionsPrivateSealed.Lawful
  :
  extensions.private.Sealed.Lawful treesync.node.leaf_node.LeafNode
  treesync.node.leaf_node.LeafNode.Insts.OpenmlsExtensionsPrivateSealed
  :=
  ⟨⟩


/-! ## Round trip of the `std` path (`RoundTripStd`, `NonEmptyStd`, `src/codec_specs.rs`)

Each type gets an `RtStd` fact (TlsCodec's `Derive/RoundTripStd.lean`: the serializer appends the
value's encoding on writers with room for its bound, and the decoder gives the value back), by
`derive_rt_std` for the derived codecs and by `RtStd.of_canon_u16` / by hand for the hand-written
`u16`-coded ones (`RoundTrip.lean`); the lemma-trait obligations follow from it. Bounds above
`2^31 - 1` use the ASSUMED `numBits_eq_64` (`imax_64`). `SignContent`, `EncryptContext` and
`ReuseGuard` derive their `PartialEq` under `cfg(hax)` only; `ReuseGuard`'s `[u8; 4]` field uses
`ArrayU8.rtStd` (`RoundTrip.lean`). -/

private theorem CT.rtStd : RtStd credentials.CredentialType.Insts.Tls_codecSerialize credentials.CredentialType.Insts.Tls_codecDeserialize 2 2 :=
  RtStd.of_canon_u16 credentials.CredentialType.Insts.Tls_codecSerialize.Lawful (fun _ => rfl)
    U16.Insts.CoreConvertFromCredentialType.from credentials.CredentialType.Insts.CoreConvertFromU16.from
    (by canon_u16_facts credentials.CredentialType.Insts.CoreCmpPartialEqCredentialType.Lawful,
      U16.Insts.CoreConvertFromCredentialType.from, credentials.CredentialType.Insts.CoreConvertFromU16.from,
      credentials.CredentialType.Insts.Tls_codecSerialize, credentials.CredentialType.Insts.Tls_codecSerialize.tls_serialize,
      credentials.CredentialType.Insts.CoreFmtDebug, credentials.CredentialType.Insts.CoreFmtDebug.fmt.ok_spec)
    (by u16_from_decodes credentials.CredentialType.Insts.Tls_codecDeserialize.tls_deserialize,
      credentials.CredentialType.Insts.CoreConvertFromU16.from)

theorem credentials.CredentialType.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful credentials.CredentialType
  credentials.CredentialType.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ credentials.CredentialType.Insts.Tls_codecSerialize.Lawful
    credentials.CredentialType.Insts.Tls_codecDeserialize.Lawful
    credentials.CredentialType.Insts.CoreCmpPartialEqCredentialType.Lawful CT.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem credentials.CredentialType.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful credentials.CredentialType
  credentials.CredentialType.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ credentials.CredentialType.Insts.Tls_codecSpecIoRoundTripStd.Lawful CT.rtStd
    (by omega) rfl

private theorem ET.rtStd : RtStd extensions.ExtensionType.Insts.Tls_codecSerialize extensions.ExtensionType.Insts.Tls_codecDeserialize 2 2 :=
  RtStd.of_canon_u16 extensions.ExtensionType.Insts.Tls_codecSerialize.Lawful (fun _ => rfl)
    U16.Insts.CoreConvertFromExtensionType.from extensions.ExtensionType.Insts.CoreConvertFromU16.from
    (by canon_u16_facts extensions.ExtensionType.Insts.CoreCmpPartialEqExtensionType.Lawful,
      U16.Insts.CoreConvertFromExtensionType.from, extensions.ExtensionType.Insts.CoreConvertFromU16.from,
      extensions.ExtensionType.Insts.Tls_codecSerialize, extensions.ExtensionType.Insts.Tls_codecSerialize.tls_serialize,
      extensions.ExtensionType.Insts.CoreFmtDebug, extensions.ExtensionType.Insts.CoreFmtDebug.fmt.ok_spec)
    (by u16_from_decodes extensions.ExtensionType.Insts.Tls_codecDeserialize.tls_deserialize,
      extensions.ExtensionType.Insts.CoreConvertFromU16.from)

theorem extensions.ExtensionType.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ extensions.ExtensionType.Insts.Tls_codecSerialize.Lawful
    extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful
    extensions.ExtensionType.Insts.CoreCmpPartialEqExtensionType.Lawful ET.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem extensions.ExtensionType.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ extensions.ExtensionType.Insts.Tls_codecSpecIoRoundTripStd.Lawful ET.rtStd
    (by omega) rfl

private theorem PT.rtStd : RtStd messages.proposals.ProposalType.Insts.Tls_codecSerialize messages.proposals.ProposalType.Insts.Tls_codecDeserialize 2 2 :=
  RtStd.of_canon_u16 messages.proposals.ProposalType.Insts.Tls_codecSerialize.Lawful (fun _ => rfl)
    U16.Insts.CoreConvertFromProposalType.from messages.proposals.ProposalType.Insts.CoreConvertFromU16.from
    (by canon_u16_facts messages.proposals.ProposalType.Insts.CoreCmpPartialEqProposalType.Lawful,
      U16.Insts.CoreConvertFromProposalType.from, messages.proposals.ProposalType.Insts.CoreConvertFromU16.from,
      messages.proposals.ProposalType.Insts.Tls_codecSerialize, messages.proposals.ProposalType.Insts.Tls_codecSerialize.tls_serialize,
      messages.proposals.ProposalType.Insts.CoreFmtDebug, messages.proposals.ProposalType.Insts.CoreFmtDebug.fmt.ok_spec)
    (by u16_from_decodes messages.proposals.ProposalType.Insts.Tls_codecDeserialize.tls_deserialize,
      messages.proposals.ProposalType.Insts.CoreConvertFromU16.from)

theorem messages.proposals.ProposalType.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful messages.proposals.ProposalType
  messages.proposals.ProposalType.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ messages.proposals.ProposalType.Insts.Tls_codecSerialize.Lawful
    messages.proposals.ProposalType.Insts.Tls_codecDeserialize.Lawful
    messages.proposals.ProposalType.Insts.CoreCmpPartialEqProposalType.Lawful PT.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem messages.proposals.ProposalType.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful messages.proposals.ProposalType
  messages.proposals.ProposalType.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ messages.proposals.ProposalType.Insts.Tls_codecSpecIoRoundTripStd.Lawful PT.rtStd
    (by omega) rfl

/-- The encoding of a `ProtocolVersion` (`Other(1)` is rejected). -/
private noncomputable def PV.out : versions.ProtocolVersion → Option (List Std.U8)
  | .Mls10 => some (Aeneas.Std.core.num.U16.to_be_bytes 1#u16).val
  | .Other v => if v = 1#u16 then none else some (Aeneas.Std.core.num.U16.to_be_bytes v).val

private theorem PV.encOut (x : versions.ProtocolVersion) :
    encOut versions.ProtocolVersion.Insts.Tls_codecSerialize x = PV.out x := by
  have := imax_ge
  refine encOut_of_runs' (sz := 2#usize) ?_ (by simp; omega)
  intro W WI hWI w hroom
  cases x with
  | Mls10 => exact U16.ser_runs 1#u16 W WI hWI w hroom
  | Other v =>
    by_cases hv : v = 1#u16
    · subst hv
      refine ⟨_, w, rfl, fun b hb => by simp [PV.out] at hb, fun _ => ⟨_, rfl⟩⟩
    · simp only [PV.out, hv, if_false]
      have h := U16.ser_runs v W WI hWI w hroom
      simp only [versions.ProtocolVersion.Insts.Tls_codecSerialize,
        versions.ProtocolVersion.Insts.Tls_codecSerialize.tls_serialize]
      split
      · exfalso; exact hv rfl
      · exact h

private theorem PV.decodes (k : Std.U16) (y : versions.ProtocolVersion)
    (hy : versions.ProtocolVersion.Insts.CoreConvertFromU16.from k = ok y) :
    DecodesTo versions.ProtocolVersion.Insts.Tls_codecDeserialize
      (Aeneas.Std.core.num.U16.to_be_bytes k).val y := by
  intro R RI v a law r rest hv
  obtain ⟨⟨res, r'⟩, hp, hres, hv'⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp
    (U16.decodes k R RI v a law r rest hv)
  simp only at hres hv'
  subst hres
  simp only [versions.ProtocolVersion.Insts.Tls_codecDeserialize.tls_deserialize]
  rw [show tls_codec.U16.Insts.Tls_codecDeserialize.tls_deserialize RI r = ok (.Ok k, r') from hp]
  simp only [bind_tc_ok, core.result.Result.map,
    P.Insts.CoreOpsFunctionFnOnceTupleU16ProtocolVersion.call_once]
  mvcgen [hy]

private theorem PV.rtStd : RtStd versions.ProtocolVersion.Insts.Tls_codecSerialize
    versions.ProtocolVersion.Insts.Tls_codecDeserialize 2 2 := by
  have := imax_ge
  refine RtStd.of_const versions.ProtocolVersion.Insts.Tls_codecSerialize.Lawful (by omega)
    (fun x => by rw [szv_eq (show versions.ProtocolVersion.Insts.Tls_codecSize.tls_serialized_len x
      = ok 2#usize from rfl)]; simp) (fun x b hb => ?_) fun x b hb => ?_
  · rw [PV.encOut] at hb
    cases x with
    | Mls10 => cases hb; simp
    | Other v =>
      by_cases hv : v = 1#u16 <;> simp only [PV.out, hv, if_true, if_false, reduceCtorEq] at hb
      cases hb; simp
  · rw [PV.encOut] at hb
    cases x with
    | Mls10 => cases hb; exact PV.decodes _ _ rfl
    | Other v =>
      by_cases hv : v = 1#u16 <;> simp only [PV.out, hv, if_true, if_false, reduceCtorEq] at hb
      cases hb
      refine PV.decodes _ _ ?_
      simp only [versions.ProtocolVersion.Insts.CoreConvertFromU16.from]
      split
      · exact absurd rfl hv
      · rfl

theorem versions.ProtocolVersion.Insts.CoreCmpPartialEqProtocolVersion.Lawful :
  core.cmp.PartialEq.Lawful versions.ProtocolVersion versions.ProtocolVersion
  versions.ProtocolVersion.Insts.CoreCmpPartialEqProtocolVersion
  := by
  u16_enum_eq_lawful versions.ProtocolVersion.Insts.CoreCmpPartialEqProtocolVersion,
    versions.ProtocolVersion.Insts.CoreCmpPartialEqProtocolVersion.eq,
    versions.ProtocolVersion.read_discriminant


theorem versions.ProtocolVersion.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful versions.ProtocolVersion
  versions.ProtocolVersion.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ versions.ProtocolVersion.Insts.Tls_codecSerialize.Lawful
    versions.ProtocolVersion.Insts.Tls_codecDeserialize.Lawful
    versions.ProtocolVersion.Insts.CoreCmpPartialEqProtocolVersion.Lawful PV.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem versions.ProtocolVersion.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful versions.ProtocolVersion
  versions.ProtocolVersion.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ versions.ProtocolVersion.Insts.Tls_codecSpecIoRoundTripStd.Lawful PV.rtStd
    (by omega) rfl

theorem ciphersuite.hash_ref.HashReference.Insts.CoreCmpPartialEqHashReference.Lawful :
  core.cmp.PartialEq.Lawful ciphersuite.hash_ref.HashReference ciphersuite.hash_ref.HashReference
  ciphersuite.hash_ref.HashReference.Insts.CoreCmpPartialEqHashReference
  := by
  derive_eq_lawful [ciphersuite.hash_ref.HashReference.Insts.CoreCmpPartialEqHashReference.eq] [VLBytes.partialEq_lawful]

private theorem HashReference.rtStd : RtStd ciphersuite.hash_ref.HashReference.Insts.Tls_codecSerialize
    ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserialize (1) (2 ^ 30 + 3) := by
  derive_rt_std (by have := imax_ge; omega) ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.Lawful
    [ciphersuite.hash_ref.HashReference.Insts.Tls_codecSerialize.tls_serialize, Shared0HashReference.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize, ciphersuite.hash_ref.HashReference.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]
    [VLBytes.rtStd]

theorem ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful ciphersuite.hash_ref.HashReference
  ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ ciphersuite.hash_ref.HashReference.Insts.Tls_codecSerialize.Lawful
    ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.hash_ref.HashReference.Insts.CoreCmpPartialEqHashReference.Lawful HashReference.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful ciphersuite.hash_ref.HashReference
  ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoRoundTripStd.Lawful HashReference.rtStd
    (by omega) rfl

theorem ciphersuite.signature.Signature.Insts.CoreCmpPartialEqSignature.Lawful :
  core.cmp.PartialEq.Lawful ciphersuite.signature.Signature ciphersuite.signature.Signature
  ciphersuite.signature.Signature.Insts.CoreCmpPartialEqSignature
  := by
  derive_eq_lawful [ciphersuite.signature.Signature.Insts.CoreCmpPartialEqSignature.eq] [VLBytes.partialEq_lawful]

private theorem Signature.rtStd : RtStd ciphersuite.signature.Signature.Insts.Tls_codecSerialize
    ciphersuite.signature.Signature.Insts.Tls_codecDeserialize (1) (2 ^ 30 + 3) := by
  derive_rt_std (by have := imax_ge; omega) ciphersuite.signature.Signature.Insts.Tls_codecSize.Lawful
    [ciphersuite.signature.Signature.Insts.Tls_codecSerialize.tls_serialize, Shared0Signature.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.signature.Signature.Insts.Tls_codecSize, ciphersuite.signature.Signature.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.signature.Signature.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]
    [VLBytes.rtStd]

theorem ciphersuite.signature.Signature.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful ciphersuite.signature.Signature
  ciphersuite.signature.Signature.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ ciphersuite.signature.Signature.Insts.Tls_codecSerialize.Lawful
    ciphersuite.signature.Signature.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.signature.Signature.Insts.CoreCmpPartialEqSignature.Lawful Signature.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem ciphersuite.signature.Signature.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful ciphersuite.signature.Signature
  ciphersuite.signature.Signature.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ ciphersuite.signature.Signature.Insts.Tls_codecSpecIoRoundTripStd.Lawful Signature.rtStd
    (by omega) rfl

theorem ciphersuite.signature.SignaturePublicKey.Insts.CoreCmpPartialEqSignaturePublicKey.Lawful :
  core.cmp.PartialEq.Lawful ciphersuite.signature.SignaturePublicKey ciphersuite.signature.SignaturePublicKey
  ciphersuite.signature.SignaturePublicKey.Insts.CoreCmpPartialEqSignaturePublicKey
  := by
  derive_eq_lawful [ciphersuite.signature.SignaturePublicKey.Insts.CoreCmpPartialEqSignaturePublicKey.eq] [VLBytes.partialEq_lawful]

private theorem SignaturePublicKey.rtStd : RtStd ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSerialize
    ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserialize (1) (2 ^ 30 + 3) := by
  derive_rt_std (by have := imax_ge; omega) ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.Lawful
    [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSerialize.tls_serialize, Shared0SignaturePublicKey.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize, ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]
    [VLBytes.rtStd]

theorem ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful ciphersuite.signature.SignaturePublicKey
  ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSerialize.Lawful
    ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.signature.SignaturePublicKey.Insts.CoreCmpPartialEqSignaturePublicKey.Lawful SignaturePublicKey.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful ciphersuite.signature.SignaturePublicKey
  ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoRoundTripStd.Lawful SignaturePublicKey.rtStd
    (by omega) rfl

theorem extensions.application_id_extension.ApplicationIdExtension.Insts.CoreCmpPartialEqApplicationIdExtension.Lawful :
  core.cmp.PartialEq.Lawful extensions.application_id_extension.ApplicationIdExtension extensions.application_id_extension.ApplicationIdExtension
  extensions.application_id_extension.ApplicationIdExtension.Insts.CoreCmpPartialEqApplicationIdExtension
  := by
  derive_eq_lawful [extensions.application_id_extension.ApplicationIdExtension.Insts.CoreCmpPartialEqApplicationIdExtension.eq] [VLBytes.partialEq_lawful]

private theorem ApplicationIdExtension.rtStd : RtStd extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize
    extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize (1) (2 ^ 30 + 3) := by
  derive_rt_std (by have := imax_ge; omega) extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.Lawful
    [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize.tls_serialize, Shared0ApplicationIdExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize, extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]
    [VLBytes.rtStd]

theorem extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful extensions.application_id_extension.ApplicationIdExtension
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize.Lawful
    extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.application_id_extension.ApplicationIdExtension.Insts.CoreCmpPartialEqApplicationIdExtension.Lawful ApplicationIdExtension.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful extensions.application_id_extension.ApplicationIdExtension
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful ApplicationIdExtension.rtStd
    (by omega) rfl

theorem extensions.external_pub_extension.ExternalPubExtension.Insts.CoreCmpPartialEqExternalPubExtension.Lawful :
  core.cmp.PartialEq.Lawful extensions.external_pub_extension.ExternalPubExtension extensions.external_pub_extension.ExternalPubExtension
  extensions.external_pub_extension.ExternalPubExtension.Insts.CoreCmpPartialEqExternalPubExtension
  := by
  derive_eq_lawful [extensions.external_pub_extension.ExternalPubExtension.Insts.CoreCmpPartialEqExternalPubExtension.eq] [VLBytes.partialEq_lawful]

private theorem ExternalPubExtension.rtStd : RtStd extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize
    extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize (1) (2 ^ 30 + 3) := by
  derive_rt_std (by have := imax_ge; omega) extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.Lawful
    [extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize.tls_serialize, Shared0ExternalPubExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize, extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]
    [VLBytes.rtStd]

theorem extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful extensions.external_pub_extension.ExternalPubExtension
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize.Lawful
    extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.external_pub_extension.ExternalPubExtension.Insts.CoreCmpPartialEqExternalPubExtension.Lawful ExternalPubExtension.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful extensions.external_pub_extension.ExternalPubExtension
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful ExternalPubExtension.rtStd
    (by omega) rfl

theorem credentials.Credential.Insts.CoreCmpPartialEqCredential.Lawful :
  core.cmp.PartialEq.Lawful credentials.Credential credentials.Credential
  credentials.Credential.Insts.CoreCmpPartialEqCredential
  := by
  derive_eq_lawful [credentials.Credential.Insts.CoreCmpPartialEqCredential.eq] [credentials.CredentialType.Insts.CoreCmpPartialEqCredentialType.Lawful, VLBytes.partialEq_lawful]

set_option maxHeartbeats 2000000 in
private theorem Credential.rtStd : RtStd credentials.Credential.Insts.Tls_codecSerialize
    credentials.Credential.Insts.Tls_codecDeserialize (2 + 1) (2 + (2 ^ 30 + 3)) := by
  derive_rt_std (by have := imax_ge; omega) credentials.Credential.Insts.Tls_codecSize.Lawful
    [credentials.Credential.Insts.Tls_codecSerialize.tls_serialize, Shared0Credential.Insts.Tls_codecSize.tls_serialized_len]
    [credentials.Credential.Insts.Tls_codecSize, credentials.Credential.Insts.Tls_codecSize.tls_serialized_len]
    [credentials.Credential.Insts.Tls_codecDeserialize.tls_deserialize]
    [credentials.CredentialType.Insts.Tls_codecSize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]
    [CT.rtStd, VLBytes.rtStd]

theorem credentials.Credential.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful credentials.Credential
  credentials.Credential.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ credentials.Credential.Insts.Tls_codecSerialize.Lawful
    credentials.Credential.Insts.Tls_codecDeserialize.Lawful
    credentials.Credential.Insts.CoreCmpPartialEqCredential.Lawful Credential.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem credentials.Credential.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful credentials.Credential
  credentials.Credential.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ credentials.Credential.Insts.Tls_codecSpecIoRoundTripStd.Lawful Credential.rtStd
    (by omega) rfl

theorem extensions.external_sender_extension.ExternalSender.Insts.CoreCmpPartialEqExternalSender.Lawful :
  core.cmp.PartialEq.Lawful extensions.external_sender_extension.ExternalSender extensions.external_sender_extension.ExternalSender
  extensions.external_sender_extension.ExternalSender.Insts.CoreCmpPartialEqExternalSender
  := by
  derive_eq_lawful [extensions.external_sender_extension.ExternalSender.Insts.CoreCmpPartialEqExternalSender.eq] [ciphersuite.signature.SignaturePublicKey.Insts.CoreCmpPartialEqSignaturePublicKey.Lawful, credentials.Credential.Insts.CoreCmpPartialEqCredential.Lawful]

set_option maxHeartbeats 2000000 in
private theorem ExternalSender.rtStd : RtStd extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSerialize
    extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize (1 + (2 + 1)) ((2 ^ 30 + 3) + (2 + (2 ^ 30 + 3))) := by
  derive_rt_std (by have := imax_64; omega) extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.Lawful
    [extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSerialize.tls_serialize, Shared0ExternalSender.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize, extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize.tls_deserialize]
    [ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSize.Lawful, credentials.Credential.Insts.Tls_codecSize.Lawful]
    [SignaturePublicKey.rtStd, Credential.rtStd]

theorem extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful extensions.external_sender_extension.ExternalSender
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSerialize.Lawful
    extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize.Lawful
    extensions.external_sender_extension.ExternalSender.Insts.CoreCmpPartialEqExternalSender.Lawful ExternalSender.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful extensions.external_sender_extension.ExternalSender
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoRoundTripStd.Lawful ExternalSender.rtStd
    (by omega) rfl

theorem extensions.last_resort.LastResortExtension.Insts.CoreCmpPartialEqLastResortExtension.Lawful :
  core.cmp.PartialEq.Lawful extensions.last_resort.LastResortExtension extensions.last_resort.LastResortExtension
  extensions.last_resort.LastResortExtension.Insts.CoreCmpPartialEqLastResortExtension
  := by
  derive_eq_lawful [extensions.last_resort.LastResortExtension.Insts.CoreCmpPartialEqLastResortExtension.eq] []

private theorem LastResort.rtStd : RtStd extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize
    extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserialize 0 0 := by
  have := imax_ge
  have hsz : ∀ x, extensions.last_resort.LastResortExtension.Insts.Tls_codecSize.tls_serialized_len x
      = ok 0#usize := fun _ => rfl
  refine RtStd.of_const extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize.Lawful
    (by omega) (fun x => by rw [szv_eq (hsz x)]; simp) (fun _ _ _ => Nat.zero_le _) fun x b hb => ?_
  have hb0 := extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize.Lawful.enc_len x _
    (hsz x) (by simp) b hb
  have hnil : b = [] := List.eq_nil_of_length_eq_zero (by simpa using hb0)
  subst hnil
  intro R RI v a law r rest hv
  simp only [extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserialize.tls_deserialize]
  exact ok_triple_of ⟨rfl, by simpa using hv⟩

theorem extensions.last_resort.LastResortExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful extensions.last_resort.LastResortExtension
  extensions.last_resort.LastResortExtension.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize.Lawful
    extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.last_resort.LastResortExtension.Insts.CoreCmpPartialEqLastResortExtension.Lawful LastResort.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.CoreCmpPartialEqRequiredCapabilitiesExtension.Lawful :
  core.cmp.PartialEq.Lawful extensions.required_capabilities.RequiredCapabilitiesExtension extensions.required_capabilities.RequiredCapabilitiesExtension
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.CoreCmpPartialEqRequiredCapabilitiesExtension
  := by
  derive_eq_lawful [extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.CoreCmpPartialEqRequiredCapabilitiesExtension.eq] [(tls_codec.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.Lawful _ extensions.ExtensionType.Insts.CoreCmpPartialEqExtensionType.Lawful), (tls_codec.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.Lawful _ messages.proposals.ProposalType.Insts.CoreCmpPartialEqProposalType.Lawful), (tls_codec.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.Lawful _ credentials.CredentialType.Insts.CoreCmpPartialEqCredentialType.Lawful)]

set_option maxHeartbeats 4000000 in
private theorem RequiredCapabilitiesExtension.rtStd : RtStd extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize
    extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize (1 + 1 + 1) ((2 ^ 30 + 3) + (2 ^ 30 + 3) + (2 ^ 30 + 3)) := by
  derive_rt_std (by have := imax_64; omega) extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.Lawful
    [extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize.tls_serialize, Shared0RequiredCapabilitiesExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize, extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize.tls_deserialize]
    [(tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ extensions.ExtensionType.Insts.Tls_codecSize.Lawful), (tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ messages.proposals.ProposalType.Insts.Tls_codecSize.Lawful), (tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ credentials.CredentialType.Insts.Tls_codecSize.Lawful)]
    [(Vec.rtStd extensions.ExtensionType.Insts.Tls_codecSpecIoNonEmptyStd extensions.ExtensionType.Insts.CoreFmtDebug extensions.ExtensionType.Insts.Tls_codecSpecIoNonEmptyStd.Lawful extensions.ExtensionType.Insts.CoreFmtDebug.Lawful), (Vec.rtStd messages.proposals.ProposalType.Insts.Tls_codecSpecIoNonEmptyStd messages.proposals.ProposalType.Insts.CoreFmtDebug messages.proposals.ProposalType.Insts.Tls_codecSpecIoNonEmptyStd.Lawful messages.proposals.ProposalType.Insts.CoreFmtDebug.Lawful), (Vec.rtStd credentials.CredentialType.Insts.Tls_codecSpecIoNonEmptyStd credentials.CredentialType.Insts.CoreFmtDebug credentials.CredentialType.Insts.Tls_codecSpecIoNonEmptyStd.Lawful credentials.CredentialType.Insts.CoreFmtDebug.Lawful)]

theorem extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful extensions.required_capabilities.RequiredCapabilitiesExtension
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize.Lawful
    extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.CoreCmpPartialEqRequiredCapabilitiesExtension.Lawful RequiredCapabilitiesExtension.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful extensions.required_capabilities.RequiredCapabilitiesExtension
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful RequiredCapabilitiesExtension.rtStd
    (by omega) rfl

theorem extensions.UnknownExtension.Insts.Tls_codecSize.Lawful :
  tls_codec.Size.Lawful extensions.UnknownExtension extensions.UnknownExtension.Insts.Tls_codecSize
  :=
  by derive_size_lawful [extensions.UnknownExtension.Insts.Tls_codecSize.tls_serialized_len] [(tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ tls_codec.U8.Insts.Tls_codecSize.Lawful)]

theorem extensions.UnknownExtension.Insts.Tls_codecSerialize.Lawful :
  tls_codec.Serialize.Lawful extensions.UnknownExtension extensions.UnknownExtension.Insts.Tls_codecSerialize
  := by
  derive_ser_std_lawful extensions.UnknownExtension.Insts.Tls_codecSize.Lawful
    [extensions.UnknownExtension.Insts.Tls_codecSerialize.tls_serialize, Shared0UnknownExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.UnknownExtension.Insts.Tls_codecSize, extensions.UnknownExtension.Insts.Tls_codecSize.tls_serialized_len]
    [(tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize.Lawful _ core.U8.Insts.CoreFmtDebug tls_codec.U8.Insts.Tls_codecSerialize.Lawful ⟨⟩)]

theorem extensions.UnknownExtension.Insts.Tls_codecDeserialize.Lawful :
  tls_codec.Deserialize.Lawful extensions.UnknownExtension extensions.UnknownExtension.Insts.Tls_codecDeserialize
  := by
  derive_de_std_lawful extensions.UnknownExtension.Insts.Tls_codecSize.Lawful
    [extensions.UnknownExtension.Insts.Tls_codecDeserialize.tls_deserialize]
    [extensions.UnknownExtension.Insts.Tls_codecSize, extensions.UnknownExtension.Insts.Tls_codecSize.tls_serialized_len]
    [(tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize.Lawful _ tls_codec.U8.Insts.Tls_codecDeserialize.Lawful)]

theorem extensions.UnknownExtension.Insts.CoreCmpPartialEqUnknownExtension.Lawful :
  core.cmp.PartialEq.Lawful extensions.UnknownExtension extensions.UnknownExtension
  extensions.UnknownExtension.Insts.CoreCmpPartialEqUnknownExtension
  := by
  derive_eq_lawful [extensions.UnknownExtension.Insts.CoreCmpPartialEqUnknownExtension.eq] [(tls_codec.alloc.vec.Vec.Insts.CoreCmpPartialEqVec.Lawful _ core.U8.Insts.CoreCmpPartialEqU8.Lawful)]

private theorem UnknownExtension.rtStd : RtStd extensions.UnknownExtension.Insts.Tls_codecSerialize
    extensions.UnknownExtension.Insts.Tls_codecDeserialize (1) (2 ^ 30 + 3) := by
  derive_rt_std_flat (by have := imax_ge; omega) extensions.UnknownExtension.Insts.Tls_codecSize.Lawful
    [extensions.UnknownExtension.Insts.Tls_codecSerialize.tls_serialize, Shared0UnknownExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.UnknownExtension.Insts.Tls_codecSize, extensions.UnknownExtension.Insts.Tls_codecSize.tls_serialized_len]
    [extensions.UnknownExtension.Insts.Tls_codecDeserialize.tls_deserialize]
    [(tls_codec.alloc.vec.Vec.Insts.Tls_codecSize.Lawful _ tls_codec.U8.Insts.Tls_codecSize.Lawful)]
    [(Vec.rtStd tls_codec.U8.Insts.Tls_codecSpecIoNonEmptyStd core.U8.Insts.CoreFmtDebug tls_codec.U8.Insts.Tls_codecSpecIoNonEmptyStd.Lawful ⟨⟩)]

theorem extensions.UnknownExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful extensions.UnknownExtension
  extensions.UnknownExtension.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ extensions.UnknownExtension.Insts.Tls_codecSerialize.Lawful
    extensions.UnknownExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.UnknownExtension.Insts.CoreCmpPartialEqUnknownExtension.Lawful UnknownExtension.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem extensions.UnknownExtension.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful extensions.UnknownExtension
  extensions.UnknownExtension.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ extensions.UnknownExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful UnknownExtension.rtStd
    (by omega) rfl

theorem ciphersuite.signature.SignContent.Insts.CoreCmpPartialEqSignContent.Lawful :
  core.cmp.PartialEq.Lawful ciphersuite.signature.SignContent ciphersuite.signature.SignContent
  ciphersuite.signature.SignContent.Insts.CoreCmpPartialEqSignContent
  := by
  derive_eq_lawful [ciphersuite.signature.SignContent.Insts.CoreCmpPartialEqSignContent.eq] [VLBytes.partialEq_lawful, VLBytes.partialEq_lawful]

private theorem SignContent.rtStd : RtStd ciphersuite.signature.SignContent.Insts.Tls_codecSerialize
    ciphersuite.signature.SignContent.Insts.Tls_codecDeserialize (1 + 1) (2 ^ 30 + 3 + (2 ^ 30 + 3)) := by
  derive_rt_std (by have := imax_64; omega) ciphersuite.signature.SignContent.Insts.Tls_codecSize.Lawful
    [ciphersuite.signature.SignContent.Insts.Tls_codecSerialize.tls_serialize, Shared0SignContent.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.signature.SignContent.Insts.Tls_codecSize, ciphersuite.signature.SignContent.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.signature.SignContent.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]
    [VLBytes.rtStd, VLBytes.rtStd]

theorem ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful ciphersuite.signature.SignContent
  ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ ciphersuite.signature.SignContent.Insts.Tls_codecSerialize.Lawful
    ciphersuite.signature.SignContent.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.signature.SignContent.Insts.CoreCmpPartialEqSignContent.Lawful SignContent.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful ciphersuite.signature.SignContent
  ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoRoundTripStd.Lawful SignContent.rtStd
    (by omega) rfl

theorem ciphersuite.hpke.EncryptContext.Insts.CoreCmpPartialEqEncryptContext.Lawful :
  core.cmp.PartialEq.Lawful ciphersuite.hpke.EncryptContext ciphersuite.hpke.EncryptContext
  ciphersuite.hpke.EncryptContext.Insts.CoreCmpPartialEqEncryptContext
  := by
  derive_eq_lawful [ciphersuite.hpke.EncryptContext.Insts.CoreCmpPartialEqEncryptContext.eq] [VLBytes.partialEq_lawful, VLBytes.partialEq_lawful]

private theorem EncryptContext.rtStd : RtStd ciphersuite.hpke.EncryptContext.Insts.Tls_codecSerialize
    ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserialize (1 + 1) (2 ^ 30 + 3 + (2 ^ 30 + 3)) := by
  derive_rt_std (by have := imax_64; omega) ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize.Lawful
    [ciphersuite.hpke.EncryptContext.Insts.Tls_codecSerialize.tls_serialize, Shared0EncryptContext.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize, ciphersuite.hpke.EncryptContext.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserialize.tls_deserialize]
    [tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful, tls_codec.quic_vec.VLBytes.Insts.Tls_codecSize.Lawful]
    [VLBytes.rtStd, VLBytes.rtStd]

theorem ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful ciphersuite.hpke.EncryptContext
  ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ ciphersuite.hpke.EncryptContext.Insts.Tls_codecSerialize.Lawful
    ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.hpke.EncryptContext.Insts.CoreCmpPartialEqEncryptContext.Lawful EncryptContext.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful ciphersuite.hpke.EncryptContext
  ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoRoundTripStd.Lawful EncryptContext.rtStd
    (by omega) rfl

theorem ciphersuite.reuse_guard.ReuseGuard.Insts.CoreCmpPartialEqReuseGuard.Lawful :
  core.cmp.PartialEq.Lawful ciphersuite.reuse_guard.ReuseGuard ciphersuite.reuse_guard.ReuseGuard
  ciphersuite.reuse_guard.ReuseGuard.Insts.CoreCmpPartialEqReuseGuard
  := by
  derive_eq_lawful [ciphersuite.reuse_guard.ReuseGuard.Insts.CoreCmpPartialEqReuseGuard.eq] [(core.Array.Insts.CoreCmpPartialEqArray.Lawful (N := 4#usize) _ core.U8.Insts.CoreCmpPartialEqU8.Lawful)]

private theorem ReuseGuard.rtStd : RtStd ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSerialize
    ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserialize (4) (4) := by
  derive_rt_std (by have := imax_ge; omega) ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.Lawful
    [ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSerialize.tls_serialize, Shared0ReuseGuard.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize, ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSize.tls_serialized_len]
    [ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserialize.tls_deserialize]
    [(tls_codec.ArrayU8LEN.Insts.Tls_codecSize.Lawful 4#usize)]
    [ArrayU8.rtStd4]

theorem ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful ciphersuite.reuse_guard.ReuseGuard
  ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSerialize.Lawful
    ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.reuse_guard.ReuseGuard.Insts.CoreCmpPartialEqReuseGuard.Lawful ReuseGuard.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful ciphersuite.reuse_guard.ReuseGuard
  ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoRoundTripStd.Lawful ReuseGuard.rtStd
    (by omega) rfl

/-- `Secret`'s constant-time `PartialEq`, through the ASSUMED spec of the opaque `equal_ct`
(`Assumptions/EqualCtSpec.lean`). -/
theorem ciphersuite.secret.Secret.Insts.CoreCmpPartialEqSecret.Lawful :
  core.cmp.PartialEq.Lawful ciphersuite.secret.Secret ciphersuite.secret.Secret
  ciphersuite.secret.Secret.Insts.CoreCmpPartialEqSecret
  := by
  have key : ∀ x y : ciphersuite.secret.Secret,
      ciphersuite.secret.Secret.Insts.CoreCmpPartialEqSecret.eq x y =
        ok (decide (x.value.vec.val = y.value.vec.val)) := by
    intro x y
    simp [ciphersuite.secret.Secret.Insts.CoreCmpPartialEqSecret.eq,
      quic_vec.secret_bytes.SecretVLBytes.as_slice, quic_vec.secret_bytes.SecretVLBytes.vec,
      core.Slice.Insts.CoreConvertAsRefSlice.as_ref, ciphersuite.equal_ct.spec,
      alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
      rust_primitives.sequence.seq_to_slice]
  constructor
  · intro x y
    simp only [key]
    refine ok_triple_of ?_
    rw [heq_iff_eq, decide_eq_true_iff]
    obtain ⟨⟨⟨a, ha⟩⟩⟩ := x
    obtain ⟨⟨⟨b, hb⟩⟩⟩ := y
    constructor
    · intro h; simp only at h; subst h; rfl
    · intro h; cases h; rfl
  · intro x y
    simp only [key, bind_tc_ok]
    exact ok_triple_of trivial


/-- `Secret`'s codec: `SecretVLBytes`'s serializer (that of `VLBytes`) and the `Vec<u8>` decoder,
which reads the same encoding (`Vec.decodes`, the `u8` element encodings being the bytes). -/
private theorem Secret.rtStd : RtStd ciphersuite.secret.Secret.Insts.Tls_codecSerialize
    ciphersuite.secret.Secret.Insts.Tls_codecDeserialize 1 (2 ^ 30 + 3) := by
  have h := VLBytes.rtStd
  refine ⟨h.room, fun x W WI hWI w hr => h.ser x.value W WI hWI w hr,
    fun x b hb => h.bound x.value b hb, fun x b hb => h.lo x.value b hb, fun x b hb => ?_⟩
  change encOut quic_vec.VLBytes.Insts.Tls_codecSerialize x.value = some b at hb
  have hx : x.value.vec.val.length ≤ 2 ^ 30 - 1 := by
    by_contra hc
    obtain ⟨e, he⟩ := VLBytes.encode_big x.value (by omega)
    rw [encOut_err he] at hb; cases hb
  obtain ⟨bv, he, hbv⟩ := VLBytes.encode_ok x.value hx
  rw [encOut_ok he, hbv, Option.some.injEq] at hb
  subst hb
  have hd := Vec.decodes U8.Insts.Tls_codecDeserialize.Lawful x.value.vec x.value.vec.val.length
    x.value.vec.val hx (encAll_u8 _) rfl (fun y _ by' hy => by
      have hy1 : encOut U8.Insts.Tls_codecSerialize y = some [y] :=
        encOut_of_runs _ y 1#usize [y] (U8.ser_runs y) (by have := imax_ge; simp; omega)
      rw [hy1, Option.some.injEq] at hy
      subst hy
      exact ⟨by simp, U8.decodes y⟩)
  intro R RI v a law r rest hv
  have hdv := hd R RI v a law r rest hv
  mvcgen [ciphersuite.secret.Secret.Insts.Tls_codecDeserialize.tls_deserialize, hdv]
  · rename_i q hq _ val _ hcf
    obtain ⟨hq1, hq2⟩ := hq
    rw [hq1] at hcf
    cases hcf
    mvcgen [quic_vec.secret_bytes.SecretVLBytes.Insts.CoreConvertFromVecU8.from,
      quic_vec.secret_bytes.SecretVLBytes.new]
  · rename_i q hq _ _ _ hbr
    rw [hq.1] at hbr
    cases hbr

theorem ciphersuite.secret.Secret.Insts.Tls_codecSpecIoRoundTripStd.Lawful :
  tls_codec.spec.io.RoundTripStd.Lawful ciphersuite.secret.Secret
  ciphersuite.secret.Secret.Insts.Tls_codecSpecIoRoundTripStd
  :=
  RoundTripStd.lawful_of_rtStd _ ciphersuite.secret.Secret.Insts.Tls_codecSerialize.Lawful
    ciphersuite.secret.Secret.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.secret.Secret.Insts.CoreCmpPartialEqSecret.Lawful Secret.rtStd (fun _ => rfl) (fun _ => rfl) rfl

theorem ciphersuite.secret.Secret.Insts.Tls_codecSpecIoNonEmptyStd.Lawful :
  tls_codec.spec.io.NonEmptyStd.Lawful ciphersuite.secret.Secret
  ciphersuite.secret.Secret.Insts.Tls_codecSpecIoNonEmptyStd
  :=
  NonEmptyStd.lawful_of_rtStd _ ciphersuite.secret.Secret.Insts.Tls_codecSpecIoRoundTripStd.Lawful Secret.rtStd
    (by omega) rfl


/-! ## Agreement of the decoders (`DecodersAgree`) and the mixed round trip (`RoundTripMixed`)

Derived structs and newtypes are chains of field decoders (TlsCodec's `Derive/DecodersAgree.lean`:
`seqStd` / `seqB`, equal to the extraction by `seq_std_eq` / `seq_b_eq`) over the fields' facts; the
hand-written codecs use `Verification/DecodersAgree.lean`. The mixed round trip follows from the
`std` round trip (`RoundTripMixed.lawful_of`). -/

theorem versions.ProtocolVersion.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful versions.ProtocolVersion
  versions.ProtocolVersion.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ versions.ProtocolVersion.Insts.Tls_codecDeserialize.Lawful
    versions.ProtocolVersion.Insts.Tls_codecDeserializeBytes.Lawful
    versions.ProtocolVersion.Insts.CoreCmpPartialEqProtocolVersion.Lawful
    PV.agree.1
    PV.agree.2
    (fun _ => rfl) rfl

theorem versions.ProtocolVersion.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful versions.ProtocolVersion
  versions.ProtocolVersion.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ versions.ProtocolVersion.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    versions.ProtocolVersion.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful credentials.CredentialType
  credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ credentials.CredentialType.Insts.Tls_codecDeserialize.Lawful
    credentials.CredentialType.Insts.Tls_codecDeserializeBytes.Lawful
    credentials.CredentialType.Insts.CoreCmpPartialEqCredentialType.Lawful
    CT.agree.1
    CT.agree.2
    (fun _ => rfl) rfl

theorem credentials.CredentialType.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful credentials.CredentialType
  credentials.CredentialType.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ credentials.CredentialType.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem extensions.ExtensionType.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful
    extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.Lawful
    extensions.ExtensionType.Insts.CoreCmpPartialEqExtensionType.Lawful
    ET.agree.1
    ET.agree.2
    (fun _ => rfl) rfl

theorem extensions.ExtensionType.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful extensions.ExtensionType
  extensions.ExtensionType.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ extensions.ExtensionType.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    extensions.ExtensionType.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem messages.proposals.ProposalType.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful messages.proposals.ProposalType
  messages.proposals.ProposalType.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ messages.proposals.ProposalType.Insts.Tls_codecDeserialize.Lawful
    messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.Lawful
    messages.proposals.ProposalType.Insts.CoreCmpPartialEqProposalType.Lawful
    PT.agree.1
    PT.agree.2
    (fun _ => rfl) rfl

theorem messages.proposals.ProposalType.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful messages.proposals.ProposalType
  messages.proposals.ProposalType.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ messages.proposals.ProposalType.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    messages.proposals.ProposalType.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful ciphersuite.hash_ref.HashReference
  ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserializeBytes.Lawful
    ciphersuite.hash_ref.HashReference.Insts.CoreCmpPartialEqHashReference.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun x =>
        AgreeF.ret ({ value := x } : ciphersuite.hash_ref.HashReference))
      (fun _ _ _ => by seq_std_eq ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun x => BIndepF.ret ({ value := x } : ciphersuite.hash_ref.HashReference)) (Agree.total VLBytes.agree.1))
      (fun _ => by seq_b_eq ciphersuite.hash_ref.HashReference.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful ciphersuite.hash_ref.HashReference
  ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    ciphersuite.hash_ref.HashReference.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem ciphersuite.signature.Signature.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful ciphersuite.signature.Signature
  ciphersuite.signature.Signature.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ ciphersuite.signature.Signature.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.signature.Signature.Insts.Tls_codecDeserializeBytes.Lawful
    ciphersuite.signature.Signature.Insts.CoreCmpPartialEqSignature.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun x =>
        AgreeF.ret ({ value := x } : ciphersuite.signature.Signature))
      (fun _ _ _ => by seq_std_eq ciphersuite.signature.Signature.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq ciphersuite.signature.Signature.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun x => BIndepF.ret ({ value := x } : ciphersuite.signature.Signature)) (Agree.total VLBytes.agree.1))
      (fun _ => by seq_b_eq ciphersuite.signature.Signature.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem ciphersuite.signature.Signature.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful ciphersuite.signature.Signature
  ciphersuite.signature.Signature.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ ciphersuite.signature.Signature.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    ciphersuite.signature.Signature.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful ciphersuite.signature.SignaturePublicKey
  ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserializeBytes.Lawful
    ciphersuite.signature.SignaturePublicKey.Insts.CoreCmpPartialEqSignaturePublicKey.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun x =>
        AgreeF.ret ({ value := x } : ciphersuite.signature.SignaturePublicKey))
      (fun _ _ _ => by seq_std_eq ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun x => BIndepF.ret ({ value := x } : ciphersuite.signature.SignaturePublicKey)) (Agree.total VLBytes.agree.1))
      (fun _ => by seq_b_eq ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful ciphersuite.signature.SignaturePublicKey
  ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem credentials.Credential.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful credentials.Credential
  credentials.Credential.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ credentials.Credential.Insts.Tls_codecDeserialize.Lawful
    credentials.Credential.Insts.Tls_codecDeserializeBytes.Lawful
    credentials.Credential.Insts.CoreCmpPartialEqCredential.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree (And.intro credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1) fun x =>
        AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun y =>
        AgreeF.ret ({ credential_type := x, serialized_credential_content := y } : credentials.Credential))
      (fun _ _ _ => by seq_std_eq credentials.Credential.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq credentials.Credential.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep (And.intro credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).2)
        (fun x => BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun y => BIndepF.ret ({ credential_type := x, serialized_credential_content := y } : credentials.Credential)) (Agree.total VLBytes.agree.1)) (Agree.total (And.intro credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1))
      (fun _ => by seq_b_eq credentials.Credential.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem credentials.Credential.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful credentials.Credential
  credentials.Credential.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ credentials.Credential.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    credentials.Credential.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful extensions.application_id_extension.ApplicationIdExtension
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserializeBytes.Lawful
    extensions.application_id_extension.ApplicationIdExtension.Insts.CoreCmpPartialEqApplicationIdExtension.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun x =>
        AgreeF.ret ({ key_id := x } : extensions.application_id_extension.ApplicationIdExtension))
      (fun _ _ _ => by seq_std_eq extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun x => BIndepF.ret ({ key_id := x } : extensions.application_id_extension.ApplicationIdExtension)) (Agree.total VLBytes.agree.1))
      (fun _ => by seq_b_eq extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful extensions.application_id_extension.ApplicationIdExtension
  extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful extensions.required_capabilities.RequiredCapabilitiesExtension
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserializeBytes.Lawful
    extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.CoreCmpPartialEqRequiredCapabilitiesExtension.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree (Vec.agree extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.Lawful extensions.ExtensionType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree extensions.ExtensionType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1) fun x =>
        AgreeF.seq (AgreeF.of_agree (Vec.agree messages.proposals.ProposalType.Insts.Tls_codecDeserialize.Lawful messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.Lawful messages.proposals.ProposalType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree messages.proposals.ProposalType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1) fun y =>
        AgreeF.seq (AgreeF.of_agree (Vec.agree credentials.CredentialType.Insts.Tls_codecDeserialize.Lawful credentials.CredentialType.Insts.Tls_codecDeserializeBytes.Lawful credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1) fun z =>
        AgreeF.ret ({ extension_types := x, proposal_types := y, credential_types := z } : extensions.required_capabilities.RequiredCapabilitiesExtension))
      (fun _ _ _ => by seq_std_eq extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep (Vec.agree extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.Lawful extensions.ExtensionType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree extensions.ExtensionType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).2)
        (fun x => BIndepF.seq (BIndepF.of_bindep (Vec.agree messages.proposals.ProposalType.Insts.Tls_codecDeserialize.Lawful messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.Lawful messages.proposals.ProposalType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree messages.proposals.ProposalType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).2)
        (fun y => BIndepF.seq (BIndepF.of_bindep (Vec.agree credentials.CredentialType.Insts.Tls_codecDeserialize.Lawful credentials.CredentialType.Insts.Tls_codecDeserializeBytes.Lawful credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).2)
        (fun z => BIndepF.ret ({ extension_types := x, proposal_types := y, credential_types := z } : extensions.required_capabilities.RequiredCapabilitiesExtension)) (Agree.total (Vec.agree credentials.CredentialType.Insts.Tls_codecDeserialize.Lawful credentials.CredentialType.Insts.Tls_codecDeserializeBytes.Lawful credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree credentials.CredentialType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1)) (Agree.total (Vec.agree messages.proposals.ProposalType.Insts.Tls_codecDeserialize.Lawful messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.Lawful messages.proposals.ProposalType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree messages.proposals.ProposalType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1)) (Agree.total (Vec.agree extensions.ExtensionType.Insts.Tls_codecDeserialize.Lawful extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.Lawful extensions.ExtensionType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree extensions.ExtensionType.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1))
      (fun _ => by seq_b_eq extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful extensions.required_capabilities.RequiredCapabilitiesExtension
  extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful extensions.external_pub_extension.ExternalPubExtension
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserializeBytes.Lawful
    extensions.external_pub_extension.ExternalPubExtension.Insts.CoreCmpPartialEqExternalPubExtension.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun x =>
        AgreeF.ret ({ external_pub := x } : extensions.external_pub_extension.ExternalPubExtension))
      (fun _ _ _ => by seq_std_eq extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun x => BIndepF.ret ({ external_pub := x } : extensions.external_pub_extension.ExternalPubExtension)) (Agree.total VLBytes.agree.1))
      (fun _ => by seq_b_eq extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful extensions.external_pub_extension.ExternalPubExtension
  extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful extensions.external_sender_extension.ExternalSender
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize.Lawful
    extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserializeBytes.Lawful
    extensions.external_sender_extension.ExternalSender.Insts.CoreCmpPartialEqExternalSender.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree (And.intro ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1) fun x =>
        AgreeF.seq (AgreeF.of_agree (And.intro credentials.Credential.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree credentials.Credential.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1) fun y =>
        AgreeF.ret ({ signature_key := x, credential := y } : extensions.external_sender_extension.ExternalSender))
      (fun _ _ _ => by seq_std_eq extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep (And.intro ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).2)
        (fun x => BIndepF.seq (BIndepF.of_bindep (And.intro credentials.Credential.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree credentials.Credential.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).2)
        (fun y => BIndepF.ret ({ signature_key := x, credential := y } : extensions.external_sender_extension.ExternalSender)) (Agree.total (And.intro credentials.Credential.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree credentials.Credential.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1)) (Agree.total (And.intro ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoDecodersAgree.Lawful.agree ciphersuite.signature.SignaturePublicKey.Insts.Tls_codecSpecIoDecodersAgree.Lawful.bindep).1))
      (fun _ => by seq_b_eq extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful extensions.external_sender_extension.ExternalSender
  extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem extensions.last_resort.LastResortExtension.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful extensions.last_resort.LastResortExtension
  extensions.last_resort.LastResortExtension.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserialize.Lawful
    extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserializeBytes.Lawful
    extensions.last_resort.LastResortExtension.Insts.CoreCmpPartialEqLastResortExtension.Lawful
    (AgreeF.congr (AgreeF.ret (() : extensions.last_resort.LastResortExtension)) (fun _ _ _ => rfl) (fun _ => rfl))
    (BIndepF.congr (BIndepF.ret (() : extensions.last_resort.LastResortExtension)) (fun _ => rfl))
    (fun _ => rfl) rfl

theorem extensions.last_resort.LastResortExtension.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful extensions.last_resort.LastResortExtension
  extensions.last_resort.LastResortExtension.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ extensions.last_resort.LastResortExtension.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    extensions.last_resort.LastResortExtension.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful ciphersuite.signature.SignContent
  ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ ciphersuite.signature.SignContent.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.signature.SignContent.Insts.Tls_codecDeserializeBytes.Lawful
    ciphersuite.signature.SignContent.Insts.CoreCmpPartialEqSignContent.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun x =>
        AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun y =>
        AgreeF.ret ({ label := x, content := y } : ciphersuite.signature.SignContent))
      (fun _ _ _ => by seq_std_eq ciphersuite.signature.SignContent.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq ciphersuite.signature.SignContent.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun x => BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun y => BIndepF.ret ({ label := x, content := y } : ciphersuite.signature.SignContent)) (Agree.total VLBytes.agree.1)) (Agree.total VLBytes.agree.1))
      (fun _ => by seq_b_eq ciphersuite.signature.SignContent.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful ciphersuite.signature.SignContent
  ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    ciphersuite.signature.SignContent.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful ciphersuite.hpke.EncryptContext
  ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserializeBytes.Lawful
    ciphersuite.hpke.EncryptContext.Insts.CoreCmpPartialEqEncryptContext.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun x =>
        AgreeF.seq (AgreeF.of_agree VLBytes.agree.1) fun y =>
        AgreeF.ret ({ label := x, context := y } : ciphersuite.hpke.EncryptContext))
      (fun _ _ _ => by seq_std_eq ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun x => BIndepF.seq (BIndepF.of_bindep VLBytes.agree.2)
        (fun y => BIndepF.ret ({ label := x, context := y } : ciphersuite.hpke.EncryptContext)) (Agree.total VLBytes.agree.1)) (Agree.total VLBytes.agree.1))
      (fun _ => by seq_b_eq ciphersuite.hpke.EncryptContext.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful ciphersuite.hpke.EncryptContext
  ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    ciphersuite.hpke.EncryptContext.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful ciphersuite.reuse_guard.ReuseGuard
  ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserializeBytes.Lawful
    ciphersuite.reuse_guard.ReuseGuard.Insts.CoreCmpPartialEqReuseGuard.Lawful
    (AgreeF.congr (AgreeF.seq (AgreeF.of_agree (ArrayU8.agree 4#usize).1) fun x =>
        AgreeF.ret ({ value := x } : ciphersuite.reuse_guard.ReuseGuard))
      (fun _ _ _ => by seq_std_eq ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => by seq_b_eq ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (BIndepF.congr (BIndepF.seq (BIndepF.of_bindep (ArrayU8.agree 4#usize).2)
        (fun x => BIndepF.ret ({ value := x } : ciphersuite.reuse_guard.ReuseGuard)) (Agree.total (ArrayU8.agree 4#usize).1))
      (fun _ => by seq_b_eq ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes))
    (fun _ => rfl) rfl

theorem ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful ciphersuite.reuse_guard.ReuseGuard
  ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    ciphersuite.reuse_guard.ReuseGuard.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl

theorem ciphersuite.secret.Secret.Insts.Tls_codecSpecIoDecodersAgree.Lawful :
  tls_codec.spec.io.DecodersAgree.Lawful ciphersuite.secret.Secret
  ciphersuite.secret.Secret.Insts.Tls_codecSpecIoDecodersAgree
  :=
  DecodersAgree.lawful_of_facts _ ciphersuite.secret.Secret.Insts.Tls_codecDeserialize.Lawful
    ciphersuite.secret.Secret.Insts.Tls_codecDeserializeBytes.Lawful
    ciphersuite.secret.Secret.Insts.CoreCmpPartialEqSecret.Lawful
    Secret.agree.1
    Secret.agree.2
    (fun _ => rfl) rfl

theorem ciphersuite.secret.Secret.Insts.Tls_codecSpecIoRoundTripMixed.Lawful :
  tls_codec.spec.io.RoundTripMixed.Lawful ciphersuite.secret.Secret
  ciphersuite.secret.Secret.Insts.Tls_codecSpecIoRoundTripMixed
  :=
  RoundTripMixed.lawful_of _ ciphersuite.secret.Secret.Insts.Tls_codecSpecIoRoundTripStd.Lawful
    ciphersuite.secret.Secret.Insts.Tls_codecSpecIoDecodersAgree.Lawful rfl rfl


end openmls
