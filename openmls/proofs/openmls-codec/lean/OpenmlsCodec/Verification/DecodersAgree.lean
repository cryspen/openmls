/- Agreement of the decoders (`DecodersAgree`) of the hand-written OpenMLS codecs whose byte-slice
decoder runs the `std` decoder on the slice (`CredentialType`, `ExtensionType`, `ProposalType`:
2 bytes read with `read_exact`, then `From<u16>`; `Secret`: a `Vec<u8>`), and of `ProtocolVersion`
(`u16` then `From<u16>` on both paths). The derived codecs use TlsCodec's
`Derive/DecodersAgree.lean` directly (`ProofObligations.lean`).

Obligations: none directly.
Axioms reached: TlsCodec's. -/
import OpenmlsCodec.Verification.RoundTrip
import TlsCodec.Verification.Derive.DecodersAgree
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace openmls
open tls_codec tls_codec.Derive

/-- `FixedRunsM` of a hand-written decoder reading 2 bytes with `read_exact`, then
`from_be_bytes` and the total `From<u16>` `fromU` (`de` its function). -/
macro "u16_from_fixedM" de:ident "," fromU:ident : tactic => `(tactic| (
  intro R RI v a law r
  have hre := read_exact_spec law r
  have hfu : ∀ u, ⦃ ⌜ True ⌝ ⦄ $fromU:ident u ⦃ ⇓ z => ⌜ $fromU:ident u = ok z ⌝ ⦄ := by
    intro u
    obtain ⟨z, hz⟩ : ∃ z, $fromU:ident u = ok z := by
      unfold $fromU:ident; split
      all_goals first
        | exact ⟨_, rfl⟩
        | (obtain ⟨b, hb⟩ := grease_total u; simp only [hb, bind_tc_ok, Aeneas.Std.bind_ok]; split <;> exact ⟨_, rfl⟩)
    rw [hz]; exact ok_triple_of rfl
  dsimp only
  mvcgen [$de:ident, hre, core.num.U16.from_be_bytes_spec, hfu, core.array.Array.as_mut_slice,
    rust_primitives.slice.array_as_mut_slice]
  · rename_i p hp _ _ _ ext1 hcf i hi z hz
    set arr := Aeneas.Std.Array.repeat 2#usize 0#u8
    have hl : (arr.to_slice_mut.1 : Slice Std.U8).val.length = 2 := to_slice_mut_len arr
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩
    · have hpe := hp.1 (by rw [hl]; simpa using h1)
      refine ⟨ext1, ?_, ?_, fun x _ => by rw [hpe, hl]; rfl⟩
      · show (arr.to_slice_mut.2 p.2.2).val = _
        rw [hpe]
        exact read_fixed arr (v r) (by simpa using h1)
      · rw [show core.num.U16.from_be_bytes ext1 = ok i from by rw [hi]; rfl]
        simp only [bind_tc_ok, Aeneas.Std.bind_ok, hz]
    · exfalso
      rw [hp.2 (by rw [hl]; simpa using h1)] at hcf
      simp [tryCF] at hcf
  · rename_i p hp _ res _ hbr
    set arr := Aeneas.Std.Array.repeat 2#usize 0#u8
    have hl : (arr.to_slice_mut.1 : Slice Std.U8).val.length = 2 := to_slice_mut_len arr
    refine try_break_vc (x := p.1) (fun e he => ?_) hbr
    by_cases h1 : 2 ≤ (v r).length
    · rw [hp.1 (by rw [hl]; exact h1)] at he; cases he
    · rw [hp.2 (by rw [hl]; omega)] at he; cases he
      rw [from_io_eof]
      refine ok_triple_of ?_
      mvcgen
      exact ⟨fun h => absurd (by simpa using h) h1, fun _ => ⟨_, rfl⟩⟩))

theorem CT.fixedM : FixedRunsM
    (fun RI r => credentials.CredentialType.Insts.Tls_codecDeserialize.tls_deserialize RI r) 2#usize
    (fun arr => do
      let i ← core.num.U16.from_be_bytes arr
      let ct ← credentials.CredentialType.Insts.CoreConvertFromU16.from i
      ok (.Ok ct)) := by
  u16_from_fixedM credentials.CredentialType.Insts.Tls_codecDeserialize.tls_deserialize,
    credentials.CredentialType.Insts.CoreConvertFromU16.from

theorem ET.fixedM : FixedRunsM
    (fun RI r => extensions.ExtensionType.Insts.Tls_codecDeserialize.tls_deserialize RI r) 2#usize
    (fun arr => do
      let i ← core.num.U16.from_be_bytes arr
      let ct ← extensions.ExtensionType.Insts.CoreConvertFromU16.from i
      ok (.Ok ct)) := by
  u16_from_fixedM extensions.ExtensionType.Insts.Tls_codecDeserialize.tls_deserialize,
    extensions.ExtensionType.Insts.CoreConvertFromU16.from

theorem PT.fixedM : FixedRunsM
    (fun RI r => messages.proposals.ProposalType.Insts.Tls_codecDeserialize.tls_deserialize RI r)
    2#usize
    (fun arr => do
      let i ← core.num.U16.from_be_bytes arr
      let ct ← messages.proposals.ProposalType.Insts.CoreConvertFromU16.from i
      ok (.Ok ct)) := by
  u16_from_fixedM messages.proposals.ProposalType.Insts.Tls_codecDeserialize.tls_deserialize,
    messages.proposals.ProposalType.Insts.CoreConvertFromU16.from

theorem CT.agree :
    AgreeF (fun RI r => credentials.CredentialType.Insts.Tls_codecDeserialize.tls_deserialize RI r)
      credentials.CredentialType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes ∧
    BIndepF credentials.CredentialType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes := by
  have h := AgreeF.of_fixedM_via 2#usize _ CT.fixedM
  exact ⟨AgreeF.congr h.1 (fun _ _ _ => rfl)
      (fun _ => by via_eq credentials.CredentialType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes),
    BIndepF.congr h.2
      (fun _ => by via_eq credentials.CredentialType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes)⟩

theorem ET.agree :
    AgreeF (fun RI r => extensions.ExtensionType.Insts.Tls_codecDeserialize.tls_deserialize RI r)
      extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes ∧
    BIndepF extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes := by
  have h := AgreeF.of_fixedM_via 2#usize _ ET.fixedM
  exact ⟨AgreeF.congr h.1 (fun _ _ _ => rfl)
      (fun _ => by via_eq extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes),
    BIndepF.congr h.2
      (fun _ => by via_eq extensions.ExtensionType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes)⟩

theorem PT.agree :
    AgreeF (fun RI r => messages.proposals.ProposalType.Insts.Tls_codecDeserialize.tls_deserialize RI r)
      messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes ∧
    BIndepF messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes := by
  have h := AgreeF.of_fixedM_via 2#usize _ PT.fixedM
  exact ⟨AgreeF.congr h.1 (fun _ _ _ => rfl)
      (fun _ => by via_eq messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes),
    BIndepF.congr h.2
      (fun _ => by via_eq messages.proposals.ProposalType.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes)⟩

theorem PV.from_total (v : Std.U16) :
    ∃ y, versions.ProtocolVersion.Insts.CoreConvertFromU16.from v = ok y := by
  unfold versions.ProtocolVersion.Insts.CoreConvertFromU16.from; split <;> exact ⟨_, rfl⟩

/-- `ProtocolVersion`: `u16`, then the total `From<u16>` (`Result::map` on the `std` path). -/
theorem PV.agree :
    AgreeF (fun RI r => versions.ProtocolVersion.Insts.Tls_codecDeserialize.tls_deserialize RI r)
      versions.ProtocolVersion.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes ∧
    BIndepF versions.ProtocolVersion.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes := by
  refine ⟨AgreeF.congr (AgreeF.seq (AgreeF.of_agree U16.agree.1) fun v =>
      AgreeF.bindRet (versions.ProtocolVersion.Insts.CoreConvertFromU16.from v) (fun y => y)
        (PV.from_total v)) (fun R RI r => ?_) (fun _ => by
      seq_b_eq versions.ProtocolVersion.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes),
    BIndepF.congr (BIndepF.seq (BIndepF.of_bindep U16.agree.2) (fun v =>
      BIndepF.bindRet (versions.ProtocolVersion.Insts.CoreConvertFromU16.from v) (fun y => y)
        (PV.from_total v)) (Agree.total U16.agree.1)) (fun _ => by
      seq_b_eq versions.ProtocolVersion.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes)⟩
  choose pvOf hpv using PV.from_total
  have hfrom : versions.ProtocolVersion.Insts.CoreConvertFromU16.from = fun v => ok (pvOf v) :=
    funext hpv
  show versions.ProtocolVersion.Insts.Tls_codecDeserialize.tls_deserialize _ _ = _
  unfold versions.ProtocolVersion.Insts.Tls_codecDeserialize.tls_deserialize seqStd
  simp only [hfrom]
  refine rustm_bind_congr fun x => ?_
  obtain ⟨res, b⟩ := x
  cases res with
  | Ok v =>
    simp [core.result.Result.map, P.Insts.CoreOpsFunctionFnOnceTupleU16ProtocolVersion.call_once, hfrom,
      Aeneas.Std.bind_ok, core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch]
  | Err e =>
    simp [core.result.Result.map, Aeneas.Std.bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultInfallibleE.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual,
      core.convert.From.Blanket, core.convert.From.Blanket.from]

/-- `Secret`: the `Vec<u8>` decoder, then `SecretVLBytes::from`; its byte-slice decoder runs the
`std` one on the slice. -/
theorem Secret.agree :
    AgreeF (fun RI r => ciphersuite.secret.Secret.Insts.Tls_codecDeserialize.tls_deserialize RI r)
      ciphersuite.secret.Secret.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes ∧
    BIndepF ciphersuite.secret.Secret.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes := by
  have hV := Vec.agree U8.Insts.Tls_codecDeserialize.Lawful U8.Insts.Tls_codecDeserializeBytes.Lawful
    U8.agree.1 U8.agree.2
  have htot : ∀ v, ∃ y, core.convert.Into.Blanket.into
      quic_vec.secret_bytes.SecretVLBytes.Insts.CoreConvertFromVecU8 v = ok y := fun v => ⟨_, rfl⟩
  have h0 := AgreeF.via (d := fun RI r => ciphersuite.secret.Secret.Insts.Tls_codecDeserialize.tls_deserialize RI r)
    (AgreeF.congr (d' := fun RI r => ciphersuite.secret.Secret.Insts.Tls_codecDeserialize.tls_deserialize RI r) (AgreeF.seq (AgreeF.of_agree hV.1) fun v =>
      AgreeF.bindRet (core.convert.Into.Blanket.into
        quic_vec.secret_bytes.SecretVLBytes.Insts.CoreConvertFromVecU8 v)
        (fun sv => ({ value := sv } : ciphersuite.secret.Secret)) (htot v))
      (fun _ _ _ => by seq_std_eq ciphersuite.secret.Secret.Insts.Tls_codecDeserialize.tls_deserialize)
      (fun _ => rfl))
    (BIndepF.seq (BIndepF.of_bindep hV.2) (fun v =>
      BIndepF.bindRet (core.convert.Into.Blanket.into
        quic_vec.secret_bytes.SecretVLBytes.Insts.CoreConvertFromVecU8 v)
        (fun sv => ({ value := sv } : ciphersuite.secret.Secret)) (htot v)) (Agree.total hV.1))
  exact ⟨AgreeF.congr h0.1 (fun _ _ _ => rfl)
      (fun _ => by via_eq ciphersuite.secret.Secret.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes),
    BIndepF.congr h0.2
      (fun _ => by via_eq ciphersuite.secret.Secret.Insts.Tls_codecDeserializeBytes.tls_deserialize_bytes)⟩

end openmls
