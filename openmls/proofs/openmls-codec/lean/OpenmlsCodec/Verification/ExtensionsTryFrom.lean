/- `Extensions<T>`'s `std` deserializer (upstream layout since 2026-08): the list is
decoded as a `Vec<ExtensionIn<T>>`, each element running `T::validate_extension_type` on its type
(total by the trait's termination contract, `ExtensionValidator.Lawful`; the error is formatted with
`ToString`, total by `ToString.Lawful`), then `Extensions::try_from` checks for duplicates
(`HashSet::insert`, model in `Assumptions/MissingStdModels.lean`) and keeps the extensions
(`map(ExtensionIn::into_extension).collect()`). On `Ok`, `unique` is the decoded list, whose size is
the `Vec<ExtensionIn<T>>`'s.

Obligations: none directly; `ProofObligations.lean` instantiates `extensions.extension_in.ExtensionIn.de_lawful_of`,
`extensions.Extensions.de_lawful_of` and `extensions.extension_in.ExtensionIn.size_lawful`.
Axioms reached (`scripts/axiom_whitelist.txt`): nothing ASSUMED; the signature-only stubs of
`ExtensionStd.lean`. -/
import OpenmlsCodec.Extraction
import OpenmlsCodec.Verification.ExtensionStdSer
import TlsCodec.Verification.Derive.Std
import TlsCodec.Verification.ProofObligations
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do
set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace openmls
open tls_codec tls_codec.Derive

/-! ## `map(f).collect::<Vec<_>>()` over a `Vec`'s `IntoIter` -/

/-- The `collect` loop over `map(f)` of a `Vec` iterator pushes the images of the remaining items. -/
theorem from_iter_loop_map {A B F : Type _} (f : A → B) (FI : core.ops.function.FnMut F A B) (g : F)
    (hf : ∀ a, FI.call_mut g a = ok (f a, g)) :
    ∀ (l : List A) (it : alloc.vec.into_iter.IntoIter A) (res : alloc.vec.Vec B),
      it.val = l → res.val.length + l.length ≤ Usize.max →
      ∃ r, alloc.vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter_loop
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
            (alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator A) FI)
          { iter := it, f := g } res = ok r ∧ r.val = res.val ++ l.map f := by
  intro l
  induction l with
  | nil =>
    intro it res hit _
    refine ⟨res, ?_, by simp⟩
    rw [alloc.vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter_loop.eq_1]
    have h0 : Slice.len it = 0#usize := by
      apply UScalar.eq_of_val_eq; simp [hit]
    simp [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
      alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
      rust_primitives.sequence.seq_len, h0]
  | cons x l ih =>
    intro it res hit hlen
    have h0 : Slice.len it ≠ 0#usize := by
      intro h; have := congrArg UScalar.val h; simp [hit] at this
    have hpos : 0 < it.val.length := by simp [hit]
    have hres : res.val.length + 1 ≤ Usize.max := by simp at hlen; omega
    obtain ⟨r, hr, hrv⟩ := ih (Slice.from it.val.tail (by have := it.property; simp; omega))
      (Slice.from (res.val ++ [f x]) (by simp; omega)) (by simp [hit]) (by simp at hlen ⊢; omega)
    refine ⟨r, ?_, by rw [hrv]; simp⟩
    rw [alloc.vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter_loop.eq_1]
    simp [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
      alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next,
      rust_primitives.sequence.seq_len, rust_primitives.sequence.seq_remove, h0, hpos, hit, hf,
      alloc.vec.Vec.push, rust_primitives.sequence.seq_push, hres]
    convert hr using 3
    simp [hit]

/-- `candidate.into_iter().map(ExtensionIn::into_extension).collect()` is the list of the
extensions. -/
theorem collect_into_extension {T E : Type _} (VI : extensions.ExtensionValidator T E)
    (cand : alloc.vec.Vec (extensions.extension_in.ExtensionIn T)) :
    ∃ v : alloc.vec.Vec extensions.Extension, (do
      let ii ← alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter cand
      let m ← core.iter.traits.iterator.Iterator.map.default
        (alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
          (extensions.extension_in.ExtensionIn T))
        (P.Insts.CoreOpsFunctionFnMutTupleExtensionInExtension VI) ii
        (extensions.extension_in.ExtensionIn.into_extension VI)
      core.iter.traits.iterator.Iterator.collect.default
        (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
          (alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator
            (extensions.extension_in.ExtensionIn T))
          (P.Insts.CoreOpsFunctionFnMutTupleExtensionInExtension VI))
        (alloc.vec.Vec.Insts.CoreIterTraitsCollectFromIterator extensions.Extension) m
      : RustM (alloc.vec.Vec extensions.Extension)) = ok v ∧ v.val = cand.val.map Prod.fst := by
  obtain ⟨r, hr, hrv⟩ := from_iter_loop_map Prod.fst
    (P.Insts.CoreOpsFunctionFnMutTupleExtensionInExtension VI)
    (extensions.extension_in.ExtensionIn.into_extension VI)
    (fun a => by
      obtain ⟨e, u⟩ := a
      simp [P.Insts.CoreOpsFunctionFnMutTupleExtensionInExtension,
        P.Insts.CoreOpsFunctionFnMutTupleExtensionInExtension.call_mut,
        extensions.extension_in.ExtensionIn.into_extension])
    cand.val cand (Slice.new _) rfl (by simp only [Slice.new_val, List.length_nil, Nat.zero_add]; exact cand.property)
  refine ⟨r, ?_, by rw [hrv]; simp⟩
  simp only [alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
    core.iter.traits.iterator.Iterator.map.default, core.iter.adapters.map.Map.new,
    core.iter.traits.iterator.Iterator.collect.default,
    alloc.vec.Vec.Insts.CoreIterTraitsCollectFromIterator,
    alloc.vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter,
    core.iter.traits.collect.IntoIterator.Blanket, core.iter.traits.collect.IntoIterator.Blanket.into_iter,
    CoreModels.alloc.vec.Vec.new, rust_primitives.sequence.seq_empty, bind_tc_ok, Aeneas.Std.bind_ok]
  exact hr

/-! ## `Extensions::try_from(Vec<ExtensionIn<T>>)` -/

/-- The `try_from` loop returns; on `Ok`, `unique` is the list of the candidate's extensions. -/
theorem try_from_loop_spec {T E : Type _} (VI : extensions.ExtensionValidator T E)
    (cand : alloc.vec.Vec (extensions.extension_in.ExtensionIn T))
    (it : core.slice.iter.Iter (extensions.extension_in.ExtensionIn T))
    (seen : std.collections.hash.set.HashSet extensions.ExtensionType
      std.hash.random.RandomState alloc.alloc.Global) :
    ⦃ ⌜ True ⌝ ⦄
    extensions.Extensions.Insts.CoreConvertTryFromVecExtensionInInvalidExtensionError.try_from_loop
      VI it cand seen
    ⦃ ⇓ r => ⌜ ∀ x, r = .Ok x → x.unique.val = cand.val.map Prod.fst ⌝ ⦄ := by
  unfold extensions.Extensions.Insts.CoreConvertTryFromVecExtensionInInvalidExtensionError.try_from_loop
  apply Aeneas.Std.WP.spec_to_mvcgen
  apply Aeneas.Std.loop.spec_decr_nat
    (fun q : core.slice.iter.Iter (extensions.extension_in.ExtensionIn T) ×
      std.collections.hash.set.HashSet extensions.ExtensionType
        std.hash.random.RandomState alloc.alloc.Global => q.1.val.length)
    (fun _ => True)
  · rintro ⟨it, u⟩ -
    obtain ⟨v, hv, hvv⟩ := collect_into_extension VI cand
    simp only [extensions.Extensions.Insts.CoreConvertTryFromVecExtensionInInvalidExtensionError.try_from_loop.body,
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next,
      rust_primitives.sequence.seq_len, rust_primitives.sequence.seq_remove]
    by_cases hl : it.val.length = 0
    · have h0 : Slice.len it = 0#usize := by scalar_tac
      simp only [h0, if_true, bind_tc_ok]
      simp only [alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter,
        core.iter.traits.iterator.Iterator.map.default, core.iter.adapters.map.Map.new,
        core.iter.traits.iterator.Iterator.collect.default,
        alloc.vec.Vec.Insts.CoreIterTraitsCollectFromIterator,
        alloc.vec.Vec.Insts.CoreIterTraitsCollectFromIterator.from_iter,
        core.iter.traits.collect.IntoIterator.Blanket, core.iter.traits.collect.IntoIterator.Blanket.into_iter,
    CoreModels.alloc.vec.Vec.new, rust_primitives.sequence.seq_empty, bind_tc_ok, Aeneas.Std.bind_ok] at hv ⊢
      simp [hv, hvv]
    · have h0 : Slice.len it ≠ 0#usize := by scalar_tac
      have hpos : 0 < it.val.length := Nat.pos_of_ne_zero hl
      simp [h0, hpos, extensions.extension_in.ExtensionIn.extension_type,
        extensions.Extension.extension_type_eq, std.collections.hash.set.HashSet.insert]
      generalize (it.val[0]'hpos) = q
      obtain ⟨e0, p0⟩ := q
      by_cases hm : e0.etOf ∈ u.elems <;> simp [hm, hpos]
  · trivial

theorem try_from_spec {T E : Type _} (VI : extensions.ExtensionValidator T E)
    (FI : core.convert.From extensions.errors.InvalidExtensionError E)
    (cand : alloc.vec.Vec (extensions.extension_in.ExtensionIn T)) :
    ⦃ ⌜ True ⌝ ⦄
    extensions.Extensions.Insts.CoreConvertTryFromVecExtensionInInvalidExtensionError.try_from VI FI cand
    ⦃ ⇓ r => ⌜ ∀ x, r = .Ok x → x.unique.val = cand.val.map Prod.fst ⌝ ⦄ := by
  simp only [extensions.Extensions.Insts.CoreConvertTryFromVecExtensionInInvalidExtensionError.try_from,
    std.collections.hash.set.HashSetTRandomStateGlobal.with_capacity,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, alloc.vec.Vec.as_slice,
    rust_primitives.sequence.seq_to_slice, core.slice.Slice.iter,
    rust_primitives.sequence.seq_from_slice, bind_tc_ok, Aeneas.Std.bind_ok]
  exact try_from_loop_spec VI cand _ _

/-! ## `ExtensionIn<T>`: `Extension` decoded with the validator check -/

theorem extensions.extension_in.ExtensionIn.size_lawful {T E : Type _}
    (VI : extensions.ExtensionValidator T E)
    (hS : Size.Lawful extensions.Extension extensions.Extension.Insts.Tls_codecSize) :
    Size.Lawful (extensions.extension_in.ExtensionIn T)
      (extensions.extension_in.ExtensionIn.Insts.Tls_codecSize VI) :=
  ⟨fun x hp => by
    obtain ⟨e, u⟩ := x
    exact hS.tls_serialized_len_spec e hp⟩

theorem extensions.extension_in.ExtensionIn.size_eq {T E : Type _}
    (VI : extensions.ExtensionValidator T E) (x : extensions.Extension)
    (p : core.marker.PhantomData T) :
    extensions.extension_in.ExtensionIn.Insts.Tls_codecSize.tls_serialized_len VI (x, p) =
      extensions.Extension.Insts.Tls_codecSize.tls_serialized_len x := rfl

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
theorem extensions.extension_in.ExtensionIn.de_runs {T E : Type _}
    (VI : extensions.ExtensionValidator T E) (TS : alloc.string.ToString E)
    (hV : extensions.ExtensionValidator.Lawful T E VI) (hTS : alloc.string.ToString.Lawful E TS) :
    DeRuns (extensions.extension_in.ExtensionIn.Insts.Tls_codecDeserialize VI TS)
      (fun _ _ _ => True) := by
  intro R RI v a law r
  have hTs := de_std_spec hT law
  have hVL := VLBytes.de_runs R RI v a law
  have hval := fun e => hV.validate_extension_type_spec e (pre_holds_of_ok_true rfl)
  have hts := hTS.to_string_spec
  have xA := extensions.codec.deserialize_extension_exact_spec hA
  have xR := extensions.codec.deserialize_extension_exact_spec hR
  have xQ := extensions.codec.deserialize_extension_exact_spec hQ
  have xP := extensions.codec.deserialize_extension_exact_spec hP
  have xE := extensions.codec.deserialize_extension_exact_spec hE
  have xL := extensions.codec.deserialize_extension_exact_spec hL
  mvcgen [extensions.extension_in.ExtensionIn.Insts.Tls_codecDeserialize,
    extensions.extension_in.ExtensionIn.Insts.Tls_codecDeserialize.tls_deserialize, hTs, hVL,
    hval, hts, core.result.Result.map_err,
    extensions.extension_in.DeserializeExtensionIn.tls_deserialize.closure.Insts.CoreOpsFunctionFnOnceTupleClause0_ErrorError,
    extensions.extension_in.DeserializeExtensionIn.tls_deserialize.closure.Insts.CoreOpsFunctionFnOnceTupleClause0_ErrorError.call_once,
    xA, xR, xQ, xP, xE, xL, quic_vec.VLBytes.as_slice, quic_vec.VLBytes.impl.vec,
    alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref, core.Slice.Insts.CoreConvertAsRefSlice.as_ref]
  all_goals first
    | (rename_i hbr; exact try_break_vc (fun e _ => by mvcgen; intro _; mvcgen; all_goals simp) hbr)
    | (intro val hval
       cases hval
       erw [extensions.extension_in.ExtensionIn.size_eq]
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
/-- `ExtensionIn<T>`'s `Deserialize.Lawful`, from the validator's, `ToString`'s and
`Extension`'s payloads'. -/
theorem extensions.extension_in.ExtensionIn.de_lawful_of {T E : Type _}
    (VI : extensions.ExtensionValidator T E) (TS : alloc.string.ToString E)
    (hV : extensions.ExtensionValidator.Lawful T E VI) (hTS : alloc.string.ToString.Lawful E TS)
    (hS : Size.Lawful extensions.Extension extensions.Extension.Insts.Tls_codecSize) :
    Deserialize.Lawful (extensions.extension_in.ExtensionIn T)
      (extensions.extension_in.ExtensionIn.Insts.Tls_codecDeserialize VI TS) :=
  de_lawful_of_runs _ (extensions.extension_in.ExtensionIn.size_lawful VI hS)
    (extensions.extension_in.ExtensionIn.de_runs hT hA hR hQ hP hE hL VI TS hV hTS)
    (fun _ _ => rfl)
end de

/-! ## `Extensions<T>` -/

/-- The size fold is preserved by a size-preserving map. -/
theorem SizeFoldRel.map {A B : Type _} {SA : Size A} {SB : Size B} (f : A → B)
    (hf : ∀ x, SB.tls_serialized_len (f x) = SA.tls_serialized_len x) {a : Std.Usize}
    {l : List A} {r : Std.Usize} (h : SizeFoldRel SA a l r) : SizeFoldRel SB a (l.map f) r := by
  induction h with
  | nil a => exact .nil a
  | cons a x l n r hx _ ih => exact .cons a (f x) _ n r (by rw [hf]; exact hx) ih

/-- Two vectors related by a size-preserving map have the same size. -/
theorem vec_size_map {A B : Type _} {SA : Size A} {SB : Size B} (hA : Size.Lawful A SA)
    (hB : Size.Lawful B SB) (f : A → B)
    (hf : ∀ x, SB.tls_serialized_len (f x) = SA.tls_serialized_len x)
    (v : alloc.vec.Vec A) (w : alloc.vec.Vec B) (hw : w.val = v.val.map f) :
    alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len SB w =
      alloc.vec.Vec.Insts.Tls_codecSize.tls_serialized_len SA v := by
  obtain ⟨r, hr, c, ll, hrel, rfl, hll⟩ := Aeneas.Std.triple_iff_exists_ok.mp
    (alloc.vec.Vec.size_rel SA hA v)
  obtain ⟨r2, hr2, c2, ll2, hrel2, rfl, hll2⟩ := Aeneas.Std.triple_iff_exists_ok.mp
    (alloc.vec.Vec.size_rel SB hB w)
  have hm := SizeFoldRel.map f hf hrel
  rw [← hw] at hm
  obtain rfl := hm.functional hrel2
  have : ll = ll2 := UScalar.eq_of_val_eq (by rw [hll, hll2])
  subst this
  rw [hr, hr2]

/-- `Extensions<T>`'s `std` `Deserialize.Lawful` (generated instance), from `ExtensionIn<T>`'s and
the `Size.Lawful`s. -/
theorem extensions.Extensions.de_lawful_of {T E : Type _} (VI : extensions.ExtensionValidator T E)
    (TS : alloc.string.ToString E)
    (FI : core.convert.From extensions.errors.InvalidExtensionError E)
    (hS : tls_codec.Size.Lawful (extensions.Extensions T) (extensions.Extensions.Insts.Tls_codecSize T))
    (hES : tls_codec.Size.Lawful extensions.Extension extensions.Extension.Insts.Tls_codecSize)
    (hI : tls_codec.Deserialize.Lawful (extensions.extension_in.ExtensionIn T)
      (extensions.extension_in.ExtensionIn.Insts.Tls_codecDeserialize VI TS)) :
    tls_codec.Deserialize.Lawful (extensions.Extensions T)
      (extensions.Extensions.Insts.Tls_codecDeserialize VI TS FI) := by
  refine de_lawful_of_runs _ hS (P := fun _ _ _ => True) ?_ (fun _ _ => rfl)
  intro R RI v a law r
  have hT := Deserialize.Lawful.runs (tls_codec.alloc.vec.Vec.Insts.Tls_codecDeserialize.Lawful _ hI)
    R RI v a law r
  have htf := fun c => try_from_spec VI FI c
  mvcgen [extensions.Extensions.Insts.Tls_codecDeserialize.tls_deserialize, hT, htf]
  · rename_i p _ u _ hcf r1 hr1 hp
    obtain ⟨n, sz, hn, h2, hsz, hszn⟩ := hp u (continue_eq_tryCF.mp hcf)
    cases r1 with
    | Ok x =>
      have hx := hr1 x rfl
      simp only [core.result.Result.map_err]
      mvcgen
      intro val hval
      cases hval
      refine ⟨n, sz, hn, h2, ?_, hszn⟩
      simp only [extensions.Extensions.Insts.Tls_codecSize.tls_serialized_len]
      rw [vec_size_map (extensions.extension_in.ExtensionIn.size_lawful VI hES) hES Prod.fst
        (fun y => by obtain ⟨e, q⟩ := y; rfl) u x.unique hx]
      exact hsz
    | Err e =>
      simp only [core.result.Result.map_err]
      mvcgen [extensions.DeserializeExtensions.tls_deserialize.closure.Insts.CoreOpsFunctionFnOnceTupleInvalidExtensionErrorError.call_once]
      · exact toStr_utf8 _ _
      · simp
  · rename_i q _ res _ hbr _
    refine try_break_vc (x := q.1) (fun e _ => ?_) hbr
    mvcgen
    intro _
    mvcgen
    all_goals simp

end openmls
