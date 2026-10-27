/- Round trip (`RoundTripStd`, `NonEmptyStd`) of the `u16`-coded OpenMLS enums with hand-written
codecs: `CredentialType`, `ExtensionType`, `ProposalType` (serializers that reject non-canonical
values, deserializers reading 2 bytes then `From<u16>`) and `ProtocolVersion`. Each gets
TlsCodec's `RtStd` fact (`Derive/RoundTripStd.lean`), from which `ProofObligations.lean` closes the
lemma-trait obligations; the derived structs over them use `derive_rt_std` directly. Also the
`RtStd` leaf of `[u8; LEN]` (the field of `ReuseGuard`).

Obligations: none directly.
Axioms reached: the ASSUMED `…CoreFmtDebug.fmt.ok_spec` of `Assumptions/FmtAssumptions.lean`
(through the serializers' rejection branch), and TlsCodec's. -/
import OpenmlsCodec.Verification.CanonicalSer
import OpenmlsCodec.Assumptions.FmtAssumptions
import TlsCodec.Verification.Derive.RoundTripStd
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace openmls
open tls_codec tls_codec.Derive

/-- `is_grease_value` is total. -/
theorem grease_total (u : Std.U16) : ∃ b, openmls_traits.grease.is_grease_value u = ok b := by
  unfold openmls_traits.grease.is_grease_value; split <;> exact ⟨_, rfl⟩

/-- The encoding of a value written with one `write_all` of `bs`. -/
theorem encOut_of_u16Ser {T : Type} {SI : Serialize T} {x : T} {bs : Slice Std.U8}
    (h : U16Ser SI x bs) : encOut SI x = some bs.val := by
  have := imax_ge
  obtain ⟨e, he, hs, -⟩ := encode_of_runs SI x 2#usize _
    (ser_runs_of_write_all SI x bs 2#usize (by rw [h.1]; rfl) h.2) (by simp; omega)
  obtain ⟨bv, rfl, hbv⟩ := hs _ rfl
  rw [encOut_ok he, hbv]

/-- The encoding of a value whose serializer runs as `o` on writers with room for `sz`. -/
theorem encOut_of_runs' {T : Type} {SI : Serialize T} {x : T} {sz : Std.Usize}
    {o : Option (List Std.U8)} (h : SerRuns SI x sz o) (hroom : sz.val ≤ imax) :
    encOut SI x = o := by
  obtain ⟨e, he, hs, hn⟩ := encode_of_runs SI x sz o h hroom
  cases o with
  | some b => obtain ⟨bv, rfl, hbv⟩ := hs b rfl; rw [encOut_ok he, hbv]
  | none => obtain ⟨err, rfl⟩ := hn rfl; exact encOut_err he

/-- A rejected value has no encoding. -/
theorem encOut_of_serErr {T : Type} {SI : Serialize T} {x : T} (h : SerErr SI x) :
    encOut SI x = none := by
  have := imax_ge
  refine encOut_of_post SI x none 0 0 (by omega) fun W WI _ w _ => ?_
  obtain ⟨e, he⟩ := h WI w
  rw [he]
  exact ok_triple_of (by simp)

/-- `RtStd` of a 2-byte codec that writes the big-endian bytes of `toU x` when `fromU` maps them
back to `x` (and rejects `x` otherwise), and whose decoder maps 2 bytes `k` to `fromU k`. -/
theorem RtStd.of_canon_u16 {T : Type} {SI : Serialize T} {DI : Deserialize T}
    (hL : Serialize.Lawful T SI) (hsz : ∀ x, SI.SizeInst.tls_serialized_len x = ok 2#usize)
    (toU : T → RustM Std.U16) (fromU : Std.U16 → RustM T)
    (hcanon : ∀ x, ∃ k, toU x = ok k ∧ ((fromU k = ok x ∧
      U16Ser SI x (Array.to_slice (Aeneas.Std.core.num.U16.to_be_bytes k))) ∨ SerErr SI x))
    (hdec : ∀ k y, fromU k = ok y → DecodesTo DI (Aeneas.Std.core.num.U16.to_be_bytes k).val y) :
    RtStd SI DI 2 2 := by
  have := imax_ge
  have henc : ∀ x b, encOut SI x = some b → ∃ k, fromU k = ok x ∧
      b = (Aeneas.Std.core.num.U16.to_be_bytes k).val := by
    intro x b hb
    obtain ⟨k, -, ⟨hf, hu⟩ | herr⟩ := hcanon x
    · rw [encOut_of_u16Ser hu] at hb
      cases hb
      exact ⟨k, hf, by simp [Array.to_slice]⟩
    · rw [encOut_of_serErr herr] at hb; cases hb
  refine RtStd.of_const hL (by omega) (fun x => by rw [szv_eq (hsz x)]; simp)
    (fun x b hb => ?_) fun x b hb => ?_
  · obtain ⟨k, -, rfl⟩ := henc x b hb; simp
  · obtain ⟨k, hk, rfl⟩ := henc x b hb; exact hdec k x hk

/-- `∀ k y, fromU k = ok y → DecodesTo DI (to_be_bytes k) y` of a hand-written decoder reading
2 bytes with `read_exact`, then `from_be_bytes` and the total `From<u16>` `fromU` (`de` its
function). -/
macro "u16_from_decodes" de:ident "," fromU:ident : tactic => `(tactic| (
  intro k y hy R RI v a law r rest hv
  have hre := read_exact_spec law r
  have hfu : ∀ u, ⦃ ⌜ True ⌝ ⦄ $fromU:ident u ⦃ ⇓ z => ⌜ $fromU:ident u = ok z ⌝ ⦄ := by
    intro u
    obtain ⟨z, hz⟩ : ∃ z, $fromU:ident u = ok z := by
      unfold $fromU:ident; split
      all_goals first
        | exact ⟨_, rfl⟩
        | (obtain ⟨b, hb⟩ := grease_total u; simp only [hb, bind_tc_ok]; split <;> exact ⟨_, rfl⟩)
    rw [hz]; exact ok_triple_of rfl
  have hl2 : (Aeneas.Std.core.num.U16.to_be_bytes k).val.length = 2 := by simp
  mvcgen [$de:ident, hre, core.num.U16.from_be_bytes_spec, hfu]
  · rename_i arr p hp _ _ _ _ _ i hi z hz
    have hl : (arr.to_slice_mut.1 : Slice Std.U8).val.length = 2 := to_slice_mut_len arr
    have h1 : 2 ≤ (v r).length := by rw [hv]; simp
    have hpe := hp.1 (by rw [hl]; exact h1)
    subst hpe
    have harr := read_fixed arr (v r) h1
    have hk : i = k := by
      rw [hi]
      have : arr.to_slice_mut.2 (alloc.io.read.cut (v r) arr.to_slice_mut.1) =
          Aeneas.Std.core.num.U16.to_be_bytes k := by
        apply Subtype.ext; rw [harr, hv]; exact List.take_left' hl2
      show Aeneas.Std.core.num.U16.from_be_bytes
        (arr.to_slice_mut.2 (alloc.io.read.cut (v r) arr.to_slice_mut.1)) = k
      rw [this, U16_from_be_bytes_to_be_bytes]
    subst hk
    rw [hy] at hz; cases hz
    refine ⟨rfl, ?_⟩
    simp only [hl]
    rw [law.adv_view r 2 h1, hv, List.drop_left' hl2]
  · rename_i arr p hp _ res _ hbr
    have hl : (arr.to_slice_mut.1 : Slice Std.U8).val.length = 2 := to_slice_mut_len arr
    have h1 : 2 ≤ (v r).length := by rw [hv]; simp
    rw [hp.1 (by rw [hl]; exact h1)] at hbr
    simp [tryCF] at hbr))

/-- The `hcanon` premise of `RtStd.of_canon_u16` for a hand-written serializer rejecting the
values that `From<u16>` maps elsewhere (arguments as `canon_u16_ser`). -/
macro "canon_u16_facts" hEq:term "," toU:ident "," fromU:ident "," ser:ident ","
    serfn:ident "," dbg:ident "," okspec:term : tactic => `(tactic| (
  intro x
  obtain ⟨k, hk⟩ : ∃ k, $toU x = ok k := by
    unfold $toU:ident; split <;> exact ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, $fromU k = ok y := by
    unfold $fromU:ident; split
    all_goals first
      | exact ⟨_, rfl⟩
      | (obtain ⟨b, hb⟩ := grease_total k; simp only [hb, bind_tc_ok]; split <;> exact ⟨_, rfl⟩)
  refine ⟨k, hk, ?_⟩
  have hne := ne_default_eq $hEq y x
  obtain ⟨_, he, hbe⟩ := Aeneas.Std.WP.triple_iff_exists_ok.mp (core.num.U16.to_be_bytes_spec k)
  by_cases hc : y = x
  · left
    subst hc
    refine ⟨hy, by simp [Array.to_slice], fun WI w w' hw => ?_⟩
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

/-! ## `[u8; LEN]` -/

theorem ArrayU8.encOut {LEN : Std.Usize} (x : Array Std.U8 LEN) (hLEN : LEN.val ≤ imax) :
    encOut (ArrayU8LEN.Insts.Tls_codecSerialize LEN) x = some x.val := by
  obtain ⟨e, he, hs, -⟩ := encode_of_runs _ x _ _ (ArrayU8.ser_runs x) hLEN
  obtain ⟨bv, rfl, hbv⟩ := hs _ rfl
  rw [encOut_ok he, hbv]

/-- `[u8; LEN]`: the `LEN` bytes, decoded back by `read_exact`. -/
theorem ArrayU8.rtStd (LEN : Std.Usize) (hLEN : LEN.val ≤ imax) :
    RtStd (ArrayU8LEN.Insts.Tls_codecSerialize LEN) (ArrayU8LEN.Insts.Tls_codecDeserialize LEN)
      LEN.val LEN.val := by
  refine RtStd.of_const (ArrayU8LEN.Insts.Tls_codecSerialize.Lawful LEN) hLEN
    (fun x => by rw [szv_eq (show ArrayU8LEN.Insts.Tls_codecSize.tls_serialized_len x = ok LEN from rfl)])
    (fun x b hb => ?_) fun x b hb => ?_
  · rw [ArrayU8.encOut x hLEN] at hb; cases hb; simpa using x.property.ge
  · rw [ArrayU8.encOut x hLEN] at hb; cases hb
    exact DecodesTo_of_fixed _ LEN (fun a => a) (ArrayU8.fixed_runs LEN) x

theorem ArrayU8.rtStd4 :
    RtStd (ArrayU8LEN.Insts.Tls_codecSerialize 4#usize) (ArrayU8LEN.Insts.Tls_codecDeserialize 4#usize)
      4 4 :=
  ArrayU8.rtStd 4#usize (by have := imax_ge; simp; omega)

end openmls
