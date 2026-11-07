/- The `std` serializer of `Extension` (hand-written, `openmls/src/extensions/codec.rs`): its
`Serialize.Lawful` from its payloads' (as hypotheses). Relies on the `vlbytes_len_len` fix (upstream #2147).

Obligations: none directly; `ProofObligations.lean` instantiates `extensions.Extension.ser_lawful_of`.
Axioms reached (`scripts/axiom_whitelist.txt`): nothing ASSUMED; 8 signature-only stubs
(`core.io.error.Error.Insts.CoreFmtDebug.fmt`, `credentials.CredentialType.Insts.CoreFmtDebug.fmt`,
`extensions.ExtensionType.Insts.CoreFmtDebug.fmt`,
`extensions.external_sender_extension.ExternalSender.Insts.CoreFmtDebug.fmt`,
`extensions.ratchet_tree_extension.RatchetTreeExtension`,
`extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSerialize.tls_serialize`,
`extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize.tls_serialized_len`,
`messages.proposals.ProposalType.Insts.CoreFmtDebug.fmt`). -/
import OpenmlsCodec.Verification.ExtensionStd
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

/-! ## Serializer

The payload serializers of `ApplicationIdExtension`, `RequiredCapabilitiesExtension`,
`ExternalPubExtension` and `LastResortExtension` are generated instances (included in
`hax.toml`); their `Lawful`s are generated obligations, proved in
`ProofObligations.lean`. -/

/-- The payload match of `Extension`'s serializer, as a function (same text as the extraction). -/
noncomputable def extensions.Extension.payloadSer {W : Type} (coreiowriteWriteInst : core.io.write.Write W)
    (self : extensions.Extension) (extension_data : alloc.vec.Vec Std.U8) :
    RustM (alloc.vec.Vec Std.U8 × core.result.Result Std.Usize tls_codec.Error) := do
  match self with
  | extensions.Extension.ApplicationId e =>
    do
    let (r2, extension_data2) ←
      extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize.tls_serialize
        alloc.vec.VecU8.Insts.CoreIoWriteWrite e extension_data
    ok (extension_data2, r2)
  | extensions.Extension.RatchetTree e =>
    do
    let (r2, extension_data2) ←
      extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSerialize.tls_serialize
        alloc.vec.VecU8.Insts.CoreIoWriteWrite e extension_data
    ok (extension_data2, r2)
  | extensions.Extension.RequiredCapabilities e =>
    do
    let (r2, extension_data2) ←
      extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize.tls_serialize
        alloc.vec.VecU8.Insts.CoreIoWriteWrite e extension_data
    ok (extension_data2, r2)
  | extensions.Extension.ExternalPub e =>
    do
    let (r2, extension_data2) ←
      extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize.tls_serialize
        alloc.vec.VecU8.Insts.CoreIoWriteWrite e extension_data
    ok (extension_data2, r2)
  | extensions.Extension.ExternalSenders e =>
    do
    let (r2, extension_data2) ←
      tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize.tls_serialize
        extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSerialize
        extensions.external_sender_extension.ExternalSender.Insts.CoreFmtDebug
        alloc.vec.VecU8.Insts.CoreIoWriteWrite e extension_data
    ok (extension_data2, r2)
  | extensions.Extension.LastResort e =>
    do
    let (r2, extension_data2) ←
      extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize.tls_serialize
        alloc.vec.VecU8.Insts.CoreIoWriteWrite e extension_data
    ok (extension_data2, r2)
  | extensions.Extension.Unknown _ e =>
    do
    let s ← alloc.vec.Vec.as_slice e
    let (r2, extension_data2) ←
      alloc.vec.VecU8.Insts.CoreIoWriteWrite.write_all extension_data s
    let r3 ←
      core.result.Result.map
        (extensions.codec.SerializeExtension.tls_serialize.closure.Insts.CoreOpsFunctionFnOnceTupleTupleUsize
        coreiowriteWriteInst) r2 e
    let r4 ←
      core.result.Result.map_err
        (extensions.codec.SerializeExtension.tls_serialize.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
        coreiowriteWriteInst) r3 ()
    ok (extension_data2, r4)

/-- `Extension`'s serializer with its payload match folded into `payloadSer`. -/
theorem extensions.Extension.tls_serialize_eq {W : Type} (coreiowriteWriteInst : core.io.write.Write W)
    (self : extensions.Extension) (writer : W) :
    extensions.Extension.Insts.Tls_codecSerialize.tls_serialize coreiowriteWriteInst self writer = (do
  let et ← extensions.Extension.extension_type self
  let (r, writer1) ←
    extensions.ExtensionType.Insts.Tls_codecSerialize.tls_serialize
      coreiowriteWriteInst et writer
  let cf ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let extension_data_len ←
      extensions.Extension.Insts.Tls_codecSize.tls_serialized_len self
    let extension_data ←
      alloc.vec.Vec.with_capacity Std.U8 extension_data_len
    let (extension_data1, r1) ←
      extensions.Extension.payloadSer coreiowriteWriteInst self extension_data
    let cf1 ← core.result.Result.Insts.CoreOpsTry_traitTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let i ← extension_data_len - 2#usize
      let i1 ← extensions.codec.vlbytes_len_len val1
      let right_val ← i - i1
      massert (val1 = right_val)
      let right_val1 ← alloc.vec.Vec.len extension_data1
      massert (val1 = right_val1)
      let (r2, writer2) ←
        tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize.tls_serialize
          tls_codec.U8.Insts.Tls_codecSerialize core.U8.Insts.CoreFmtDebug
          coreiowriteWriteInst extension_data1 writer1
      let r3 ←
        core.result.Result.map
          (extensions.codec.SerializeExtension.tls_serialize.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize
          coreiowriteWriteInst) r2 val
      ok (r3, writer2)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
          Std.Usize (core.convert.From.Blanket tls_codec.Error) residual
      ok (r2, writer1)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r1 ←
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
        Std.Usize (core.convert.From.Blanket tls_codec.Error) residual
    ok (r1, writer1)) := rfl

/-- `openmls_traits::grease::is_grease_value` as a pure function. -/
def isGreaseB (u : Std.U16) : Bool :=
  match (openmls_traits.grease.is_grease_value u).match with
  | .ok b => b
  | _ => false

theorem is_grease_value_eq (u : Std.U16) :
    openmls_traits.grease.is_grease_value u = ok (isGreaseB u) := by
  obtain ⟨b, hb⟩ : ∃ b, openmls_traits.grease.is_grease_value u = ok b := by
    unfold openmls_traits.grease.is_grease_value; split <;> exact ⟨_, rfl⟩
  simp [isGreaseB, hb]

/-- The extension type of an `Extension` (`extension_type` as a pure function; upstream maps a
GREASE-valued `Unknown` to `Grease`). -/
def extensions.Extension.etOf : extensions.Extension → extensions.ExtensionType
  | .ApplicationId _ => .ApplicationId
  | .RatchetTree _ => .RatchetTree
  | .RequiredCapabilities _ => .RequiredCapabilities
  | .ExternalPub _ => .ExternalPub
  | .ExternalSenders _ => .ExternalSenders
  | .LastResort _ => .LastResort
  | .Unknown kind _ => if isGreaseB kind then .Grease kind else .Unknown kind

theorem extensions.Extension.extension_type_eq (x : extensions.Extension) :
    extensions.Extension.extension_type x = ok x.etOf := by
  cases x <;> try rfl
  simp only [extensions.Extension.extension_type, is_grease_value_eq, bind_tc_ok,
    Aeneas.Std.bind_ok, extensions.Extension.etOf]
  split <;> rfl

/-- The size of the payload of an `Extension`. -/
noncomputable def extensions.Extension.pSize : extensions.Extension → Nat
  | .ApplicationId e => (szv extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize e).val
  | .RatchetTree e => (szv extensions.ratchet_tree_extension.RatchetTreeExtension.Insts.Tls_codecSize e).val
  | .RequiredCapabilities e => (szv extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize e).val
  | .ExternalPub e => (szv extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize e).val
  | .ExternalSenders e =>
    (szv (tls_codec.alloc.vec.Vec.Insts.Tls_codecSize extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSize) e).val
  | .LastResort e => (szv extensions.last_resort.LastResortExtension.Insts.Tls_codecSize e).val
  | .Unknown _ e => e.val.length

/-- The encoding of the payload of an `Extension` (`none`: its serializer fails). -/
noncomputable def extensions.Extension.pOut : extensions.Extension → Option (List Std.U8)
  | .ApplicationId e => encOut extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize e
  | .RatchetTree e => encOut extensions.ratchet_tree_extension.RatchetTreeExtension.serializeInst e
  | .RequiredCapabilities e => encOut extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize e
  | .ExternalPub e => encOut extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize e
  | .ExternalSenders e => encOut (tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSerialize extensions.external_sender_extension.ExternalSender.Insts.CoreFmtDebug) e
  | .LastResort e => encOut extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize e
  | .Unknown _ e => some e.val

/-- The encoding of an `Extension`: type, varint length of the payload encoding, payload. -/
noncomputable def extensions.Extension.out (x : extensions.Extension) : Option (List Std.U8) :=
  (encOut extensions.ExtensionType.Insts.Tls_codecSerialize x.etOf).bind fun tb =>
    x.pOut.bind fun b =>
      if b.length ≤ 2 ^ 30 - 1 then some (tb ++ varint.enc b.length ++ b) else none

section ser
variable
  (hA : Serialize.Lawful extensions.application_id_extension.ApplicationIdExtension extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize)
  (hR : Serialize.Lawful extensions.ratchet_tree_extension.RatchetTreeExtension extensions.ratchet_tree_extension.RatchetTreeExtension.serializeInst)
  (hQ : Serialize.Lawful extensions.required_capabilities.RequiredCapabilitiesExtension extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize)
  (hP : Serialize.Lawful extensions.external_pub_extension.ExternalPubExtension extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize)
  (hE : Serialize.Lawful (alloc.vec.Vec extensions.external_sender_extension.ExternalSender) (tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize extensions.external_sender_extension.ExternalSender.Insts.Tls_codecSerialize extensions.external_sender_extension.ExternalSender.Insts.CoreFmtDebug))
  (hL : Serialize.Lawful extensions.last_resort.LastResortExtension extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize)

include hA hR hQ hP hE hL in
/-- The payload serializer on a fresh vector. -/
theorem extensions.Extension.payloadSer_runs {W : Type} (WI : core.io.write.Write W)
    (x : extensions.Extension) (hroom : x.pSize ≤ imax) :
    ∃ d r1, extensions.Extension.payloadSer WI x (Slice.new Std.U8) = ok (d, r1) ∧
      (∀ b, x.pOut = some b → ∃ n : Std.Usize, r1 = .Ok n ∧ n.val = b.length ∧ d.val = b) ∧
      (x.pOut = none → ∃ e, r1 = .Err e) := by
  cases x
  case Unknown g e =>
    change alloc.vec.Vec Std.U8 at e
    have hs : rust_primitives.sequence.seq_to_slice e = ok e := rfl
    obtain ⟨l, hl, hlv⟩ : ∃ l : Std.Usize, alloc.vec.Vec.len e = ok l ∧ l.val = e.val.length :=
      ⟨_, rfl, by simp⟩
    refine ⟨_, _, by
      simp only [extensions.Extension.payloadSer, alloc.vec.Vec.as_slice, hs, bind_tc_ok,
        Aeneas.Std.bind_ok]
      rw [StdIo.vec_write_all_eq, dif_pos (by simpa using e.property)]
      simp [Aeneas.Std.bind_ok, core.result.Result.map, core.result.Result.map_err,
        extensions.codec.SerializeExtension.tls_serialize.closure.Insts.CoreOpsFunctionFnOnceTupleTupleUsize.call_once,
        hl, Slice.new_val]
      exact ⟨rfl, rfl⟩,
      fun b hb => ?_, fun hn => by cases hn⟩
    cases hb
    exact ⟨_, rfl, hlv, rfl⟩
  all_goals
    rename_i e
    first
      | have hr := (hA.runs e _ (size_ok hA.SizeInstLawful e))
      | have hr := (hR.runs e _ (size_ok hR.SizeInstLawful e))
      | have hr := (hQ.runs e _ (size_ok hQ.SizeInstLawful e))
      | have hr := (hP.runs e _ (size_ok hP.SizeInstLawful e))
      | have hr := (hE.runs e _ (size_ok hE.SizeInstLawful e))
      | have hr := (hL.runs e _ (size_ok hL.SizeInstLawful e))
    obtain ⟨r, w', h, hs, hn⟩ := hr _ _ StdIo.vec_lawful (Slice.new Std.U8)
      (by rw [StdIo.vec_sink]; simpa [extensions.Extension.pSize] using hroom)
    refine ⟨w', r, ?_, fun b hb => ?_, hn⟩
    · first
        | (dsimp only [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize,
            extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize,
            extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize,
            extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize,
            extensions.ratchet_tree_extension.RatchetTreeExtension.serializeInst,
            tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize] at h
           simp only [extensions.Extension.payloadSer, h, bind_tc_ok, Aeneas.Std.bind_ok]; rfl)
    · obtain ⟨⟨n, hn1, hn2⟩, hv⟩ := hs b hb
      rw [StdIo.vec_sink, StdIo.vec_sink] at hv
      exact ⟨n, hn1, hn2, by simpa using hv⟩
include hA hR hQ hP hE hL in
/-- `Extension`'s size from its payload's: `2 + lenOf p + p` when it fits `isize::MAX`. -/
theorem extensions.Extension.size_val (x : extensions.Extension) :
    ∃ s : Std.Usize, extensions.Extension.Insts.Tls_codecSize.tls_serialized_len x = ok s ∧
      (s.val ≤ imax → s.val = 2 + varint.lenOf x.pSize + x.pSize) := by
  have tail : ∀ p : Std.Usize, ∃ s : Std.Usize, (do
      let k ← extensions.codec.vlbytes_len_len p
      let i ← len_add 2#usize k
      len_add i p : RustM Std.Usize) = ok s ∧
      (s.val ≤ imax → s.val = 2 + varint.lenOf p.val + p.val) := by
    intro p
    obtain ⟨k, hk, hkv⟩ := extensions.codec.vlbytes_len_len_ok p
    refine ⟨lenAddVal (lenAddVal 2#usize k) p, by simp [hk, len_add_ok], fun hle => ?_⟩
    have h1 := imax_eq
    have hm1 := lenAddVal_min 2#usize k
    have hm2 := lenAddVal_min (lenAddVal 2#usize k) p
    have h2v : (2#usize : Std.Usize).val = 2 := rfl
    rw [h2v] at hm1
    rw [← hkv]; omega
  cases x
  case Unknown g e =>
    change alloc.vec.Vec Std.U8 at e
    obtain ⟨l, hl, hlv⟩ : ∃ l : Std.Usize, alloc.vec.Vec.len e = ok l ∧ l.val = e.val.length :=
      ⟨_, rfl, by simp⟩
    obtain ⟨s, hs, hsv⟩ := tail l
    refine ⟨s, ?_, fun hle => by rw [hsv hle, hlv]; rfl⟩
    simp only [extensions.Extension.Insts.Tls_codecSize.tls_serialized_len, hl, Aeneas.Std.bind_ok]
    exact hs
  all_goals
    rename_i e
    first
      | have hz := size_ok hA.SizeInstLawful e
      | have hz := size_ok hR.SizeInstLawful e
      | have hz := size_ok hQ.SizeInstLawful e
      | have hz := size_ok hP.SizeInstLawful e
      | have hz := size_ok hE.SizeInstLawful e
      | have hz := size_ok hL.SizeInstLawful e
    obtain ⟨s, hs, hsv⟩ := tail _
    refine ⟨s, ?_, hsv⟩
    first
      | (dsimp only [extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSerialize, extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSerialize, extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSerialize, extensions.last_resort.LastResortExtension.Insts.Tls_codecSerialize, extensions.ratchet_tree_extension.RatchetTreeExtension.serializeInst,
           tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize, extensions.application_id_extension.ApplicationIdExtension.Insts.Tls_codecSize,
           extensions.required_capabilities.RequiredCapabilitiesExtension.Insts.Tls_codecSize, extensions.external_pub_extension.ExternalPubExtension.Insts.Tls_codecSize, extensions.last_resort.LastResortExtension.Insts.Tls_codecSize,
           tls_codec.alloc.vec.Vec.Insts.Tls_codecSize] at hz
         simp only [extensions.Extension.Insts.Tls_codecSize.tls_serialized_len, hz, Aeneas.Std.bind_ok]
         exact hs)

include hA hR hQ hP hE hL in
/-- The payload encoding has the payload size. -/
theorem extensions.Extension.pOut_len (x : extensions.Extension) (hroom : x.pSize ≤ imax) :
    ∀ b, x.pOut = some b → b.length = x.pSize := by
  cases x
  case Unknown g e => intro b hb; cases hb; rfl
  all_goals
    rename_i e
    first
      | exact hA.enc_len e _ (size_ok hA.SizeInstLawful e) hroom
      | exact hR.enc_len e _ (size_ok hR.SizeInstLawful e) hroom
      | exact hQ.enc_len e _ (size_ok hQ.SizeInstLawful e) hroom
      | exact hP.enc_len e _ (size_ok hP.SizeInstLawful e) hroom
      | exact hE.enc_len e _ (size_ok hE.SizeInstLawful e) hroom
      | exact hL.enc_len e _ (size_ok hL.SizeInstLawful e) hroom

include hA hR hQ hP hE hL in
/-- `Extension`'s serializer: on every lawful writer with room it writes `x.out`. -/
theorem extensions.Extension.ser_runs
    (hT : Serialize.Lawful extensions.ExtensionType extensions.ExtensionType.Insts.Tls_codecSerialize)
    (x : extensions.Extension) :
    ∃ sz, extensions.Extension.Insts.Tls_codecSerialize.SizeInst.tls_serialized_len x = ok sz ∧
      (sz.val ≤ imax → ∀ b, x.out = some b → b.length = sz.val) ∧
      SerRuns extensions.Extension.Insts.Tls_codecSerialize x sz x.out := by
  obtain ⟨sz, hsz, hszv⟩ := extensions.Extension.size_val hA hR hQ hP hE hL x
  have h2v : (2#usize : Std.Usize).val = 2 := rfl
  have hET : ∀ tb, encOut extensions.ExtensionType.Insts.Tls_codecSerialize x.etOf = some tb → tb.length = 2 :=
    fun tb htb => hT.enc_len x.etOf 2#usize rfl (by have := imax_ge; omega) tb htb
  refine ⟨sz, hsz, fun hle b hb => ?_, ?_⟩
  · have hv := hszv hle
    have hpl := extensions.Extension.pOut_len hA hR hQ hP hE hL x (by omega)
    unfold extensions.Extension.out at hb
    cases htb : encOut extensions.ExtensionType.Insts.Tls_codecSerialize x.etOf with
    | none => simp [htb] at hb
    | some tb =>
      cases hpb : x.pOut with
      | none => simp [htb, hpb] at hb
      | some b' =>
        simp only [htb, hpb, Option.bind_some] at hb
        split at hb
        · cases hb
          simp only [List.length_append, varint.enc_length, hET tb htb, hpl b' hpb]; omega
        · cases hb
  intro W WI hWI w hroom
  have hv := hszv (by omega)
  have himax := imax_eq
  have hge := imax_ge
  have hpl := extensions.Extension.pOut_len hA hR hQ hP hE hL x (by omega)
  obtain ⟨r0, w1, h0, hs0, hn0⟩ := hT.runs x.etOf 2#usize rfl W WI hWI w (by omega)
  dsimp only [extensions.ExtensionType.Insts.Tls_codecSerialize] at h0
  obtain ⟨d, r1, hp, hps, hpn⟩ :=
    extensions.Extension.payloadSer_runs hA hR hQ hP hE hL WI x (by omega)
  have hcap : alloc.vec.Vec.with_capacity Std.U8 sz = ok (Slice.new Std.U8) := by
    simp [CoreModels.alloc.vec.Vec.with_capacity, CoreModels.alloc.vec.Vec.new,
      rust_primitives.sequence.seq_empty, Aeneas.Std.bind_ok, Aeneas.Std.bind_tc_ok]
  have hvl : ∀ n : Std.Usize, ⦃ ⌜ True ⌝ ⦄ extensions.codec.vlbytes_len_len n
      ⦃ ⇓ k => ⌜ k.val = varint.lenOf n.val ⌝ ⦄ := fun n => by
    obtain ⟨k, hk, hkv⟩ := extensions.codec.vlbytes_len_len_ok n
    rw [hk]; exact ok_triple_of hkv
  -- the length prefix and content of the payload bytes
  obtain ⟨vsz, hvsz, -⟩ := Aeneas.Std.triple_iff_exists_ok.mp
    (alloc.vec.Vec.size_rel U8.Insts.Tls_codecSize U8.lawful.SizeInstLawful d)
  obtain ⟨c, -, hc, hvszv⟩ := Vec.size_exact U8.lawful d vsz hvsz (SizeNat.u8 d.val)
  have hdl : d.val.length ≤ Usize.max := d.property
  suffices H : ⦃ ⌜ True ⌝ ⦄ extensions.Extension.Insts.Tls_codecSerialize.tls_serialize WI x w
      ⦃ ⇓ p => ⌜ (∀ b, x.out = some b → (∃ n : Std.Usize, p.1 = .Ok n ∧ n.val = b.length) ∧
          core.io.write.Write.view WI p.2 = core.io.write.Write.view WI w ++ b) ∧
        (x.out = none → ∃ e, p.1 = .Err e) ⌝ ⦄ by
    obtain ⟨⟨r, w'⟩, h1, h2⟩ := Aeneas.Std.triple_iff_exists_ok.mp H
    exact ⟨r, w', h1, h2⟩
  have hVs : ∀ w' : W, ⦃ ⌜ (core.io.write.Write.view WI w').length + vsz.val ≤ imax ⌝ ⦄
      tls_codec.alloc.vec.Vec.Insts.Tls_codecSerialize.tls_serialize U8.Insts.Tls_codecSerialize
        core.U8.Insts.CoreFmtDebug WI d w'
      ⦃ ⇓ p => ⌜ (∀ b, vecOut varint.enc U8.Insts.Tls_codecSerialize d.val d.val.length = some b →
          (∃ n : Std.Usize, p.1 = .Ok n ∧ n.val = b.length) ∧
          core.io.write.Write.view WI p.2 = core.io.write.Write.view WI w' ++ b) ∧
        (vecOut varint.enc U8.Insts.Tls_codecSerialize d.val d.val.length = none →
          ∃ e, p.1 = .Err e) ⌝ ⦄ := fun w' =>
    SerRuns.spec' (Vec.ser_runs write_length_runs core.U8.Insts.CoreFmtDebug U8.lawful d vsz hvsz
      (SizeNat.u8 d.val)) WI hWI w'
  have hET0 : ∀ e, r0 = .Err e → x.out = none := by
    intro e he
    unfold extensions.Extension.out
    cases htb : encOut extensions.ExtensionType.Insts.Tls_codecSerialize x.etOf with
    | none => rfl
    | some tb => obtain ⟨⟨n, hn, -⟩, -⟩ := hs0 tb htb; rw [he] at hn; cases hn
  have hP0 : ∀ e, r1 = .Err e → x.out = none := by
    intro e he
    unfold extensions.Extension.out
    cases hpb : x.pOut with
    | none => cases encOut extensions.ExtensionType.Insts.Tls_codecSerialize x.etOf <;> rfl
    | some b => obtain ⟨n, hn, -⟩ := hps b hpb; rw [he] at hn; cases hn
  have key : ∀ v0 v1 : Std.Usize, core.ops.control_flow.ControlFlow.Continue v0 = tryCF r0 →
      core.ops.control_flow.ControlFlow.Continue v1 = tryCF r1 →
      ∃ tb b, encOut extensions.ExtensionType.Insts.Tls_codecSerialize x.etOf = some tb ∧ tb.length = 2 ∧
        core.io.write.Write.view WI w1 = core.io.write.Write.view WI w ++ tb ∧ v0.val = 2 ∧
        x.pOut = some b ∧ v1.val = b.length ∧ d.val = b ∧ b.length = x.pSize ∧
        varint.lenOf v1.val = varint.lenOf x.pSize := by
    intro v0 v1 hc0 hc1
    rw [continue_eq_tryCF] at hc0 hc1
    obtain ⟨tb, htb⟩ : ∃ tb, encOut extensions.ExtensionType.Insts.Tls_codecSerialize x.etOf = some tb := by
      cases htb : encOut extensions.ExtensionType.Insts.Tls_codecSerialize x.etOf with
      | none => obtain ⟨e, he⟩ := hn0 htb; rw [hc0] at he; cases he
      | some tb => exact ⟨tb, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, x.pOut = some b := by
      cases hpb : x.pOut with
      | none => obtain ⟨e, he⟩ := hpn hpb; rw [hc1] at he; cases he
      | some b => exact ⟨b, rfl⟩
    obtain ⟨⟨n0, hn0e, hn0l⟩, hw1⟩ := hs0 tb htb
    rw [hc0] at hn0e; cases hn0e
    obtain ⟨n1, hn1e, hn1l, hd⟩ := hps b hb
    rw [hc1] at hn1e; cases hn1e
    exact ⟨tb, b, htb, hET tb htb, hw1, by rw [hn0l, hET tb htb], hb, hn1l, hd, hpl b hb,
      by rw [hn1l, hpl b hb]⟩
  rw [extensions.Extension.tls_serialize_eq, extensions.Extension.extension_type_eq]
  mvcgen [h0, hsz, hcap, hp, hvl, hVs]
  all_goals first
    | (rename_i hbr
       exact try_break_vc (fun e he => by
         have hn : x.out = none := by first | exact hET0 e he | exact hP0 e he
         mvcgen; intro _; mvcgen; all_goals simp [hn]) hbr)
    | (name_conts r0 r1
       obtain ⟨tb, b, htb, htbl, hw1, hv0, hpb, hv1, hd, hbl, hlv⟩ := key _ _ hc0 hc1
       have hdv : d.val.length = x.pSize := by rw [hd, hbl]
       have hcp : c.val = x.pSize := by rw [hc, ← hdv]; exact min_eq_left hdl
       rw [hcp] at hvszv
       have hl8 := varint.lenOf_le x.pSize
       first
         | (rw [hw1, List.length_append, htbl]; split at hvszv <;> omega)
         | (exfalso; omega)
         | (exfalso; name_neg hne; apply hne; apply UScalar.eq_of_val_eq
            have hsl : (Slice.len d).val = d.val.length := Slice.len_val d
            subst_vars; omega)
         | (guard_target_has core.result.Result.map
            name_hyp_with tls_codec.vecOut hvec
            obtain ⟨hsome, hnone⟩ := hvec
            have hmx : UScalar.max UScalarTy.Usize = Usize.max := by
              simp [Usize.max, UScalar.max, UScalarTy.numBits, Usize.numBits]
            by_cases h30 : b.length ≤ 2 ^ 30 - 1
            · have hvo : vecOut varint.enc U8.Insts.Tls_codecSerialize d.val d.val.length =
                  some (varint.enc b.length ++ b) := by
                simp only [vecOut, hd]; rw [if_pos (by omega)]; simp [encAll_u8]
              obtain ⟨⟨n2, hn2, hn2l⟩, hw2⟩ := hsome _ hvo
              have hout : x.out = some (tb ++ varint.enc b.length ++ b) := by
                unfold extensions.Extension.out
                rw [htb, hpb]; simp only [Option.bind_some]
                split_ifs; rfl
              simp only [List.length_append, varint.enc_length, hbl] at hn2l
              rw [hn2]
              mvcgen [core.result.Result.map,
                extensions.codec.SerializeExtension.tls_serialize.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once]
              all_goals first
                | (refine ⟨fun b' hb' => ?_, fun hn => by rw [hout] at hn; cases hn⟩
                   rw [hout] at hb'; cases hb'
                   refine ⟨⟨_, rfl, ?_⟩, ?_⟩
                   · simp only [List.length_append, varint.enc_length, htbl, hbl]; omega
                   · rw [hw2, hw1]; simp only [List.append_assoc])
                | (exfalso; omega)
            · have hvo : vecOut varint.enc U8.Insts.Tls_codecSerialize d.val d.val.length = none :=
                vecOut_none_big _ _ _ (by omega)
              obtain ⟨e2, he2⟩ := hnone hvo
              have hout : x.out = none := by
                unfold extensions.Extension.out
                rw [htb, hpb]; simp only [Option.bind_some]
                split_ifs; rfl
              rw [he2]
              mvcgen [core.result.Result.map]
              all_goals first
                | (refine ⟨fun b' hb' => ?_, fun _ => ⟨e2, rfl⟩⟩
                   rw [hout] at hb'; cases hb')))

include hA hR hQ hP hE hL in
/-- `Extension`'s `Serialize.Lawful`, from its payloads' and `ExtensionType`'s. -/
theorem extensions.Extension.ser_lawful_of
    (hS : Size.Lawful extensions.Extension extensions.Extension.Insts.Tls_codecSize)
    (hT : Serialize.Lawful extensions.ExtensionType extensions.ExtensionType.Insts.Tls_codecSerialize) :
    Serialize.Lawful extensions.Extension extensions.Extension.Insts.Tls_codecSerialize :=
  ser_lawful_of_runs _ hS extensions.Extension.out
    (extensions.Extension.ser_runs hA hR hQ hP hE hL hT) (fun _ => rfl)
end ser

end openmls
