/- `Serialize.Lawful` of the hand-written `u16`-coded serializers that reject non-canonical values
(upstream OpenMLS 2026-08: `CredentialType`, `ProposalType`, `ExtensionType`, `ProtocolVersion`):
for each value, either the serializer writes 2 bytes with one `write_all` (canonical), or it returns
`Err` without touching the writer (the value decodes as a different one, e.g. `Unknown(1)`).
The encoding (`encOut`) is `none` in the second case, so the bytes / `std` agreement and the length
posts are vacuous there.

Obligations: none directly; used by `ProofObligations.lean`.
Axioms reached: none beyond TlsCodec's `Derive/Std.lean`. -/
import OpenmlsCodec.Extraction
import TlsCodec.Verification.Derive.Std
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace openmls
open tls_codec tls_codec.Derive

/-- `x` serializes as the 2 bytes `bs`, written with one `write_all`. -/
def U16Ser {T : Type _} (SI : Serialize T) (x : T) (bs : Slice Std.U8) : Prop :=
  bs.val.length = 2 ∧ ∀ {W : Type} (WI : core.io.write.Write W) (w w' : W),
    WI.write_all w bs = ok (.Ok (), w') → SI.tls_serialize WI x w = ok (.Ok 2#usize, w')

/-- `x`'s serializer returns `Err`, leaving the writer unchanged. -/
def SerErr {T : Type _} (SI : Serialize T) (x : T) : Prop :=
  ∀ {W : Type} (WI : core.io.write.Write W) (w : W), ∃ e, SI.tls_serialize WI x w = ok (.Err e, w)

open Classical in
/-- `Serialize.Lawful` of a 2-byte serializer that either writes or rejects each value. -/
theorem ser_lawful_u16_or_err {T : Type _} (SI : Serialize T) (hS : Size.Lawful T SI.SizeInst)
    (hsz : ∀ x, SI.SizeInst.tls_serialized_len x = ok 2#usize)
    (h : ∀ x, (∃ bs, U16Ser SI x bs) ∨ SerErr SI x)
    (hdet : ∀ x, SI.tls_serialize_detached x = Serialize.tls_serialize_detached.default SI x) :
    Serialize.Lawful T SI := by
  refine ser_lawful_of_runs SI hS
    (fun x => if hx : ∃ bs, U16Ser SI x bs then some (Classical.choose hx).val else none)
    (fun x => ⟨2#usize, hsz x, fun _ b hb => ?_, ?_⟩) hdet
  · split at hb
    · rename_i hx
      cases hb
      exact (Classical.choose_spec hx).1
    · cases hb
  · split
    · rename_i hx
      obtain ⟨hl, hw⟩ := Classical.choose_spec hx
      exact ser_runs_of_write_all SI x _ 2#usize (by rw [hl]; rfl) hw
    · rename_i hx
      have he : SerErr SI x := (h x).resolve_left hx
      intro W WI _ w _
      obtain ⟨e, hser⟩ := he WI w
      refine ⟨_, w, hser, fun b hb => ?_, fun _ => ⟨e, rfl⟩⟩
      simp [hx] at hb

open Classical in
/-- `PartialEq::ne` of a lawful `PartialEq` decides `≠`. -/
theorem ne_default_eq {T : Type _} {PI : core.cmp.PartialEq T T} (h : core.cmp.PartialEq.Lawful T T PI)
    (x y : T) : core.cmp.PartialEq.ne.default PI x y = ok (decide (x ≠ y)) := by
  obtain ⟨b, hb, hbv⟩ := Aeneas.Std.triple_iff_exists_ok.mp (h.eq_spec x y)
  simp only [core.cmp.PartialEq.ne.default, hb, bind_tc_ok, Aeneas.Std.bind_ok]
  congr 1
  cases b <;> simp_all

/-- `str::to_string` (the text is not modelled: the empty string). -/
theorem str_to_string_ok (s : Str) :
    alloc.string.ToString.Blanket.to_string core.Str.Insts.CoreFmtDisplay s = ok "" := by
  simp [alloc.string.ToString.Blanket.to_string, core.Str.Insts.CoreFmtDisplay,
    core.Str.Insts.CoreFmtDisplay.fmt, bind_tc_ok, Aeneas.Std.bind_ok]
  rfl

end openmls
