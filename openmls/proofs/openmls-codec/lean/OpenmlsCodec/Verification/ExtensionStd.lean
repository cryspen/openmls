/- The `std` deserializer of `Extension` (hand-written, `openmls/src/extensions/codec.rs`): its
`Deserialize.Lawful` from its payloads' (as hypotheses). Relies on the `vlbytes_len_len` fix (upstream #2147: `vlbytes_len_len`
agrees with tls_codec's varint length, `varint.lenOf`). Also the size lemmas shared with
`ExtensionStdSer.lean`.

Obligations: none directly; `ProofObligations.lean` instantiates `extensions.Extension.de_lawful_of`.
Axioms reached (`scripts/axiom_whitelist.txt`): nothing ASSUMED; 4 signature-only stubs
(`core.io.error.Error.Insts.CoreFmtDebug.fmt`,
`extensions.ratchet_tree_extension.RatchetTreeExtension`,
`extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecDeserialize.tls_deserialize`,
`extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize.tls_serialized_len`);
`native_decide` (1). -/
import OpenmlsCodec.Extraction
import TlsCodec.Verification.Derive.HandWritten
import TlsCodec.Verification.Std.SecretFrom
import OpenmlsCodec.Assumptions.RatchetTreeSpecs
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

/-- `vlbytes_len_len` is tls_codec's varint length (upstream #2147). -/
theorem extensions.codec.vlbytes_len_len_ok (n : Std.Usize) :
    ∃ k : Std.Usize, extensions.codec.vlbytes_len_len n = ok k ∧ k.val = varint.lenOf n.val := by
  unfold extensions.codec.vlbytes_len_len varint.lenOf
  split
  · exact ⟨_, rfl, by rename_i h; simp at h; simp [h]⟩
  · split
    · exact ⟨_, rfl, by rename_i h1 h2; simp at h1 h2; simp [h2]; omega⟩
    · split
      · exact ⟨_, rfl, by rename_i h1 h2 h3; simp at h1 h2 h3; split_ifs <;> simp <;> omega⟩
      · exact ⟨_, rfl, by rename_i h1 h2 h3; simp at h1 h2 h3; split_ifs <;> simp <;> omega⟩

/-- The size computation of `Extension` from its payload size `p` (when it fits a varint). -/
theorem extensions.Extension.size_tail (p : Std.Usize) (hp : p.val ≤ 2 ^ 30 - 1) :
    ∃ s : Std.Usize, (do
      let k ← extensions.codec.vlbytes_len_len p
      let i ← len_add 2#usize k
      len_add i p : RustM Std.Usize) = ok s ∧ s.val = 2 + varint.lenOf p.val + p.val := by
  obtain ⟨k, hk, hkv⟩ := extensions.codec.vlbytes_len_len_ok p
  have hl := varint.lenOf_le p.val
  refine ⟨lenAddVal (lenAddVal 2#usize k) p, by simp [hk, len_add_ok], ?_⟩
  have h2 : (lenAddVal 2#usize k).val = 2 + k.val := lenAddVal_val _ _ (by simp; scalar_tac)
  rw [lenAddVal_val _ _ (by rw [h2]; scalar_tac), h2, hkv]

/-- `T::tls_deserialize_exact(data)` (`deserialize_extension_exact`), from `T`'s
`Deserialize.Lawful`: an `Ok v` has the size of `data`. -/
theorem extensions.codec.deserialize_extension_exact_spec {T : Type} {DI : Deserialize T}
    (h : Deserialize.Lawful T DI) (s : Slice Std.U8) :
    ⦃ ⌜ True ⌝ ⦄ extensions.codec.deserialize_extension_exact DI s
    ⦃ ⇓ r => ⌜ ∀ v, r = .Ok v → (szv DI.SizeInst v).val = s.val.length ⌝ ⦄ := by
  unfold extensions.codec.deserialize_extension_exact
  exact Deserialize.Lawful.exact_slice h s

/-- The size of an `Extension` whose payload (of instance `Sz`, wrapped by `C`) has size `L`
(a varint-encodable length). -/
theorem extensions.Extension.size_arm {T : Type} {Sz : Size T} (hS : Size.Lawful T Sz)
    (C : T → extensions.Extension)
    (hC : ∀ e, extensions.Extension.Insts.Tls_codecSize.tls_serialized_len (C e) = (do
      let p ← Sz.tls_serialized_len e
      let k ← extensions.codec.vlbytes_len_len p
      let i ← len_add 2#usize k
      len_add i p))
    (e : T) (L : Nat) (hL : L ≤ 2 ^ 30 - 1) (he : (szv Sz e).val = L) :
    ∃ s : Std.Usize, extensions.Extension.Insts.Tls_codecSize.tls_serialized_len (C e) = ok s ∧
      s.val = 2 + varint.lenOf L + L := by
  obtain ⟨s, hs, hsv⟩ := extensions.Extension.size_tail (szv Sz e) (by omega)
  refine ⟨s, ?_, by rw [hsv, he]⟩
  rw [hC, size_ok hS e]
  simpa only [bind_tc_ok] using hs

/-- The size of an `Extension::Unknown` with a varint-encodable payload. -/
theorem extensions.Extension.size_unknown (g : Std.U16) (e : alloc.vec.Vec Std.U8)
    (hL : e.val.length ≤ 2 ^ 30 - 1) :
    ∃ s : Std.Usize,
      extensions.Extension.Insts.Tls_codecSize.tls_serialized_len (.Unknown g e) = ok s ∧
      s.val = 2 + varint.lenOf e.val.length + e.val.length := by
  obtain ⟨l, hl, hlv⟩ : ∃ l : Std.Usize, alloc.vec.Vec.len e = ok l ∧ l.val = e.val.length :=
    ⟨_, rfl, by simp⟩
  obtain ⟨s, hs, hsv⟩ := extensions.Extension.size_tail l (by omega)
  refine ⟨s, ?_, by rw [hsv, hlv]⟩
  simp only [extensions.Extension.Insts.Tls_codecSize.tls_serialized_len, hl, bind_tc_ok]
  exact hs

/-- The success VC of `Extension`'s deserializer: type (2 bytes), then a `VLBytes` of length `L`
(prefix `lenOf L`), then a value `x` of size `2 + lenOf L + L`. -/
theorem extensions.Extension.de_close {R : Type} {RI : alloc.io.read.Read R}
    {v : R → List Std.U8} {a : R → Nat → R} (law : StdIo.RLaw RI v a) {r : R}
    {p1 : core.result.Result extensions.ExtensionType tls_codec.Error × R}
    (hp1 : DePost extensions.ExtensionType.Insts.Tls_codecSize v a r p1)
    {et : extensions.ExtensionType} (hc1 : core.ops.control_flow.ControlFlow.Continue et = tryCF p1.1)
    {p2 : core.result.Result quic_vec.VLBytes tls_codec.Error × R}
    (hp2 : ∀ val, p2.1 = .Ok val → ∃ n sz, n ≤ (v p1.2).length ∧ p2.2 = a p1.2 n ∧
      quic_vec.VLBytes.Insts.Tls_codecSize.tls_serialized_len val = ok sz ∧ sz.val = n ∧
      VLDe (v p1.2) val n)
    {vb : quic_vec.VLBytes} (hc2 : core.ops.control_flow.ControlFlow.Continue vb = tryCF p2.1)
    (x : extensions.Extension)
    (hx : vb.vec.val.length ≤ 2 ^ 30 - 1 → ∃ s : Std.Usize,
      extensions.Extension.Insts.Tls_codecSize.tls_serialized_len x = ok s ∧
      s.val = 2 + varint.lenOf vb.vec.val.length + vb.vec.val.length) :
    ∃ n sz, n ≤ (v r).length ∧ p2.2 = a r n ∧
      extensions.Extension.Insts.Tls_codecSize.tls_serialized_len x = ok sz ∧ sz.val = n := by
  obtain ⟨res1, r1⟩ := p1
  obtain ⟨res2, r2⟩ := p2
  simp only at hc1 hc2 hp2 ⊢
  rw [continue_eq_tryCF] at hc1 hc2
  subst hc1 hc2
  have h2 : szv extensions.ExtensionType.Insts.Tls_codecSize et = 2#usize := szv_eq rfl
  rw [DePost_ok, h2] at hp1
  obtain ⟨hle1, rfl⟩ := hp1
  obtain ⟨n, sz, hn, rfl, -, -, -, hL, -, hnv⟩ := hp2 vb rfl
  obtain ⟨s, hs, hsv⟩ := hx hL
  refine ⟨2 + n, s, adv_le law hle1 hn, adv_adv' law hle1 hn, hs, by rw [hsv, hnv]; omega⟩

/-- The payload of the deserialized `Extension` has the `VLBytes`' length. -/
theorem extensions.Extension.arm_len {T : Type} {Sz : Size T} {r2 : core.result.Result T tls_codec.Error}
    {val2 : T} {s : Slice Std.U8} {vb : quic_vec.VLBytes}
    (h : ∀ v, r2 = .Ok v → (szv Sz v).val = s.val.length)
    (hc : core.ops.control_flow.ControlFlow.Continue val2 = tryCF r2) (hs : s = vb.vec) :
    (szv Sz val2).val = vb.vec.val.length := by
  rw [h val2 (continue_eq_tryCF.mp hc), hs]

/-- The `Unknown` arm: the payload is a copy of the `VLBytes`. -/
theorem extensions.Extension.size_unknown' (g : Std.U16) (r : alloc.vec.Vec Std.U8)
    (s : Slice Std.U8) (vb : quic_vec.VLBytes) (h1 : (r : Slice Std.U8) = s) (h2 : s = vb.vec)
    (hL : vb.vec.val.length ≤ 2 ^ 30 - 1) :
    ∃ s : Std.Usize,
      extensions.Extension.Insts.Tls_codecSize.tls_serialized_len (.Unknown g r) = ok s ∧
      s.val = 2 + varint.lenOf vb.vec.val.length + vb.vec.val.length := by
  have hr : r.val = vb.vec.val := by rw [← h2, ← h1]
  rw [← hr] at hL ⊢
  exact extensions.Extension.size_unknown g r hL

section de
variable
  (hT : Deserialize.Lawful extensions.ExtensionType extensions.ExtensionType.Insts.Tls_codecDeserialize)
  (hA : Deserialize.Lawful extensions.application_id_extension.ApplicationIdExtension
    extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecDeserialize)
  (hR : Deserialize.Lawful extensions.ratchet_tree_extension.RatchetTreeExtension
    extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecDeserialize)
  (hQ : Deserialize.Lawful extensions.required_capabilities.RequiredCapabilitiesExtension
    extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecDeserialize)
  (hP : Deserialize.Lawful extensions.external_pub_extension.ExternalPubExtension
    extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecDeserialize)
  (hE : Deserialize.Lawful (alloc.vec.Vec extensions.external_sender_extension.ExternalSender)
    (tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize
      extensions.external_sender_extension.ExternalSender.Insts.Tls_codecDeserialize))
  (hL : Deserialize.Lawful extensions.last_resort.LastResortExtension
    extensions.last_resort.LastResortExtension.Insts.Tls_codecDeserialize)

include hT hA hR hQ hP hE hL in
theorem extensions.Extension.de_runs :
    DeRuns extensions.Extension.Insts.Tls_codecDeserialize (fun _ _ _ => True) := by
  intro R RI v a law r
  have hTs := de_std_spec hT law
  have hVL := VLBytes.de_runs R RI v a law
  have xA := extensions.codec.deserialize_extension_exact_spec hA
  have xR := extensions.codec.deserialize_extension_exact_spec hR
  have xQ := extensions.codec.deserialize_extension_exact_spec hQ
  have xP := extensions.codec.deserialize_extension_exact_spec hP
  have xE := extensions.codec.deserialize_extension_exact_spec hE
  have xL := extensions.codec.deserialize_extension_exact_spec hL
  mvcgen [extensions.Extension.Insts.Tls_codecDeserialize,
    extensions.Extension.Insts.Tls_codecDeserialize.tls_deserialize, hTs, hVL,
    xA, xR, xQ, xP, xE, xL, quic_vec.VLBytes.as_slice, quic_vec.VLBytes.impl.vec,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, core.Slice.Insts.CoreConvertAsRefSlice.as_ref]
  all_goals first
    | (rename_i hbr; exact try_break_vc (fun e _ => by mvcgen; intro _; mvcgen; all_goals simp) hbr)
    | (intro val hval
       cases hval
       refine extensions.Extension.de_close law (by assumption) (by assumption) (by assumption)
         (by assumption) _ (fun hlen => ?_)
       first
         | exact extensions.Extension.size_arm hA.SizeInstLawful _ (fun _ => rfl) _ _ hlen
             (extensions.Extension.arm_len (by assumption) (by assumption) (by assumption))
         | exact extensions.Extension.size_arm hR.SizeInstLawful _ (fun _ => rfl) _ _ hlen
             (extensions.Extension.arm_len (by assumption) (by assumption) (by assumption))
         | exact extensions.Extension.size_arm hQ.SizeInstLawful _ (fun _ => rfl) _ _ hlen
             (extensions.Extension.arm_len (by assumption) (by assumption) (by assumption))
         | exact extensions.Extension.size_arm hP.SizeInstLawful _ (fun _ => rfl) _ _ hlen
             (extensions.Extension.arm_len (by assumption) (by assumption) (by assumption))
         | exact extensions.Extension.size_arm hE.SizeInstLawful _ (fun _ => rfl) _ _ hlen
             (extensions.Extension.arm_len (by assumption) (by assumption) (by assumption))
         | exact extensions.Extension.size_arm hL.SizeInstLawful _ (fun _ => rfl) _ _ hlen
             (extensions.Extension.arm_len (by assumption) (by assumption) (by assumption))
         | exact extensions.Extension.size_unknown' _ _ _ _ (by assumption) (by assumption) hlen)
include hT hA hR hQ hP hE hL in
/-- `Extension`'s `Deserialize.Lawful`, from its payloads' and `ExtensionType`'s. -/
theorem extensions.Extension.de_lawful_of
    (hS : Size.Lawful extensions.Extension extensions.Extension.Insts.Tls_codecSize) :
    Deserialize.Lawful extensions.Extension extensions.Extension.Insts.Tls_codecDeserialize :=
  de_lawful_of_runs _ hS (extensions.Extension.de_runs hT hA hR hQ hP hE hL) (fun _ _ => rfl)
end de

end openmls
