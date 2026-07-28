-- [openmls]: PURE / MEMBERSHIP-FORM COMPANION SPECS.
-- Charter: some extracted functions carry official monadic postconditions that are painful to
-- *consume* at a call site — they are phrased over `Result Bool` predicate programs, positional
-- `index`-based quantifiers, or closure-typed `Iterator::all` obligations.  The official
-- obligations remain in `Proofs.lean` (that is the audit surface); this file holds the *convenient*
-- pure/membership-shaped restatements that downstream proofs actually use.
--
-- Statements here are PENDING USER VALIDATION.  Nothing in this file is `@[spec]`-registered while
-- its proof is still `sorry`: registering a sorried spec would let `mvcgen` discharge a function's
-- own verification condition with that function's (unproved) spec, silently closing the obligation.
import Aeneas
import CoreModels
import Openmls.Extraction.Types
import Openmls.Extraction.Funs
import Openmls.Extraction.Specs
import Openmls.Proofs.Common
import Openmls.Proofs.BitMath
import Openmls.Proofs.PartialSpecs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

noncomputable section

namespace openmls

set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace binary_tree.array_representation.treemath

/-! ### Value specs for the verification-transparent functions

The Rust `to_tree_index` / `leaf_count` (and the `u32` dispatcher over them) carry no
`ensures` any more — their postcondition *is* their one-line body (user ruling 2026-07-28:
"transparent to verification"). Each keeps exactly ONE `@[spec]` registration: the
value-carrying mvcgen triple below (moved here from `PartialSpecs.lean`; proof combinators
still live there). -/

/-- `LeafNodeIndex::to_tree_index` is `self * 2`. **Fallible:** the multiplication overflows when
`2·self > u32::MAX`, so the contract carries a `willFail Error.integerOverflow` hypothesis — in
hypothesis position the bound is recovered rather than discharged. -/
@[spec]
theorem LeafNodeIndex.to_tree_index_mvcgen_spec (self : LeafNodeIndex)
    (Q : PostCond Std.U32 Aeneas.Std.WP.Result.postShape)
    (h_ok : ∀ r : Std.U32, (↑r : Nat) = 2 * (↑self : Nat) → Aeneas.Std.WP.willYield r Q)
    (h_fail : Std.UScalar.max .U32 < 2 * (↑self : Nat) →
      Aeneas.Std.WP.willFail Aeneas.Std.Error.integerOverflow Q) :
    ⦃ ⌜ True ⌝ ⦄ LeafNodeIndex.to_tree_index self ⦃ Q ⦄ := by
  have h2u : ((2#u32 : Std.U32) : Nat) = 2 := by scalar_tac
  unfold LeafNodeIndex.to_tree_index
  refine triple_of_partialSpec (Std.U32.mul_spec (x := self) (y := 2#u32)) Q ?_ ?_ (by simp)
  · intro r hr
    exact h_ok r (by rw [hr, h2u]; omega)
  · intro e he
    have hcase : e = Aeneas.Std.Error.integerOverflow ∧
        Std.UScalar.max .U32 < 2 * (↑self : Nat) := by
      cases e <;> simp_all; omega
    rw [hcase.1]; exact h_fail hcase.2

/-- `ParentNodeIndex::to_tree_index` is `self * 2 + 1`. **Fallible:** either the doubling or the
increment can overflow; both are covered by the single bound `2·self + 1 > u32::MAX`. -/
@[spec]
theorem ParentNodeIndex.to_tree_index_mvcgen_spec (self : ParentNodeIndex)
    (Q : PostCond Std.U32 Aeneas.Std.WP.Result.postShape)
    (h_ok : ∀ r : Std.U32, (↑r : Nat) = 2 * (↑self : Nat) + 1 → Aeneas.Std.WP.willYield r Q)
    (h_fail : Std.UScalar.max .U32 < 2 * (↑self : Nat) + 1 →
      Aeneas.Std.WP.willFail Aeneas.Std.Error.integerOverflow Q) :
    ⦃ ⌜ True ⌝ ⦄ ParentNodeIndex.to_tree_index self ⦃ Q ⦄ := by
  have h1u : ((1#u32 : Std.U32) : Nat) = 1 := by scalar_tac
  have h2u : ((2#u32 : Std.U32) : Nat) = 2 := by scalar_tac
  have hp : Aeneas.Std.WP.partialSpec
      (binary_tree.array_representation.treemath.ParentNodeIndex.to_tree_index self)
      (fun r => (↑r : Nat) = 2 * (↑self : Nat) + 1)
      (fun e => e = Aeneas.Std.Error.integerOverflow ∧
        Std.UScalar.max .U32 < 2 * (↑self : Nat) + 1) False := by
    unfold ParentNodeIndex.to_tree_index
    refine partialSpec_bind_fail
      (partialSpec_weaken (Std.U32.mul_spec (x := self) (y := 2#u32))
        (fun a ha => ha) (fun e he => ?_)) ?_
    · cases e <;> simp_all; omega
    · intro m hm
      have hmv : (↑m : Nat) = 2 * (↑self : Nat) := by rw [hm, h2u]; omega
      refine partialSpec_weaken (Std.U32.add_spec (x := m) (y := 1#u32))
        (fun a ha => ?_) (fun e he => ?_)
      · rw [ha, h1u, hmv]
      · cases e <;> simp_all
  refine triple_of_partialSpec hp Q h_ok ?_ (by simp)
  intro e he
  rw [he.1]; exact h_fail he.2

/-- `TreeNodeIndex::u32` dispatches on the constructor to `to_tree_index`. **Fallible** in both
branches (the doubling can overflow). -/
@[spec]
theorem TreeNodeIndex.u32_mvcgen_spec (self : TreeNodeIndex)
    (Q : PostCond Std.U32 Aeneas.Std.WP.Result.postShape)
    (h_ok : ∀ r : Std.U32, (↑r : Nat) = (match self with
        | TreeNodeIndex.Leaf l => 2 * (↑l : Nat)
        | TreeNodeIndex.Parent p => 2 * (↑p : Nat) + 1) →
      Aeneas.Std.WP.willYield r Q)
    (h_fail : Std.UScalar.max .U32 < (match self with
        | TreeNodeIndex.Leaf l => 2 * (↑l : Nat)
        | TreeNodeIndex.Parent p => 2 * (↑p : Nat) + 1) →
      Aeneas.Std.WP.willFail Aeneas.Std.Error.integerOverflow Q) :
    ⦃ ⌜ True ⌝ ⦄ TreeNodeIndex.u32 self ⦃ Q ⦄ := by
  unfold TreeNodeIndex.u32
  cases self with
  | Leaf l =>
    exact LeafNodeIndex.to_tree_index_mvcgen_spec l Q
      (fun r hr => h_ok r (by simpa using hr)) (fun h => h_fail (by simpa using h))
  | Parent p =>
    exact ParentNodeIndex.to_tree_index_mvcgen_spec p Q
      (fun r hr => h_ok r (by simpa using hr)) (fun h => h_fail (by simpa using h))

/-- `TreeSize::leaf_count` is `self / 2 + 1`. Total: the divisor is the literal `2`, and
`self / 2 + 1 ≤ 2^31` always fits a `u32`, so neither step can fail. -/
@[spec]
theorem TreeSize.leaf_count_mvcgen_spec (self : TreeSize)
    (Q : PostCond Std.U32 Aeneas.Std.WP.Result.postShape)
    (h_ok : ∀ r : Std.U32, (↑r : Nat) = (↑self : Nat) / 2 + 1 →
      Aeneas.Std.WP.willYield r Q) :
    ⦃ ⌜ True ⌝ ⦄ TreeSize.leaf_count self ⦃ Q ⦄ := by
  refine triple_of_partialSpec (p_fail := fun _ => False) (p_div := False) ?_ Q h_ok
    (by simp) (by simp)
  unfold TreeSize.leaf_count
  refine partialSpec_bind
    (partialSpec_of_spec (Std.U32.div_spec.step_spec (x := self) (y := 2#u32) (by simp))) ?_
  intro q hq
  refine partialSpec_imp
    (partialSpec_of_spec (Std.U32.add_spec.step_spec (x := q) (y := 1#u32) ?_)) ?_
  · simp only [hq]; scalar_tac
  · intro a ha; rw [ha, hq]; scalar_tac

/-! ### Monadic helpers about the extracted functions (moved here from `Proofs.lean`) -/

/-- `LeafNodeIndex.to_tree_index w = 2·w` (no overflow when `w < 2^31`). -/
theorem mul2_ok (w : Std.U32) (hw : (↑w : Nat) < 2 ^ 31) :
    ∃ v : Std.U32, LeafNodeIndex.to_tree_index w = ok v ∧ (↑v : Nat) = 2 * (↑w : Nat) := by
  unfold LeafNodeIndex.to_tree_index
  rw [show (w * 2#u32 : Aeneas.Std.Result Std.U32) = Aeneas.Std.UScalar.mul w 2#u32 from rfl]
  have hspec := Aeneas.Std.UScalar.mul_equiv w 2#u32
  have hmax : (↑w : Nat) * (↑(2#u32) : Nat) ≤ Aeneas.Std.UScalar.max .U32 := by
    have h2 : (↑(2#u32) : Nat) = 2 := rfl
    have hm : Aeneas.Std.UScalar.max .U32 = 2 ^ 32 - 1 := by native_decide
    rw [h2, hm]; omega
  cases hm : (Aeneas.Std.UScalar.mul w 2#u32) with
  | ok v =>
    rw [hm] at hspec
    obtain ⟨_, hv, _⟩ := hspec
    exact ⟨v, rfl, by rw [hv]; scalar_tac⟩
  | fail e =>
    rw [hm] at hspec; exfalso; omega
  | div => rw [hm] at hspec; exact hspec.elim

/-- Shared arithmetic for the `from_tree_index ((xn << k) + (1 << (k-1)) - 1)` tail of
    `lowest_common_ancestor`, given `loop0`'s postcondition (`2 ≤ k ≤ 30`, `xn·2^k < 2^30`):
    the two shifts don't wrap, their sum stays below `2^32`, `xn<<k` is even, and `1<<(k-1)`
    is an even value `≥ 2` (so the final `−1` is odd and positive). -/
theorem lca_tail_aux {p : Std.U32 × Std.I32} {i6 i8 : Std.U32} {i7 : Std.I32}
    (hk2 : 2 ≤ IScalar.toNat p.2) (hk30 : IScalar.toNat p.2 ≤ 30)
    (hbnd : (↑p.1 : Nat) * 2 ^ IScalar.toNat p.2 < 2 ^ 30)
    (hi6v : (↑i6 : Nat) = ↑p.1 <<< IScalar.toNat p.2 % UScalar.size UScalarTy.U32)
    (hi7 : (↑i7 : Int) = ↑p.2 - ↑(1#i32))
    (hi8v : (↑i8 : Nat) = ↑(1#u32) <<< IScalar.toNat i7 % UScalar.size UScalarTy.U32) :
    (↑i6 : Nat) + ↑i8 < 2 ^ 32 ∧ 2 ∣ (↑i6 : Nat) ∧ 2 ≤ (↑i8 : Nat) ∧ 2 ∣ (↑i8 : Nat) := by
  have hi7t1 : 1 ≤ IScalar.toNat i7 := by scalar_tac
  have hi7t : IScalar.toNat i7 ≤ 29 := by scalar_tac
  have hsz : (2 : Nat) ^ 31 < UScalar.size UScalarTy.U32 := by native_decide
  have h1u : (↑(1#u32) : Nat) = 1 := rfl
  have hi6val : (↑i6 : Nat) = ↑p.1 * 2 ^ IScalar.toNat p.2 := by
    rw [hi6v, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hi8val : (↑i8 : Nat) = 2 ^ IScalar.toNat i7 := by
    have hb : (2 : Nat) ^ IScalar.toNat i7 < UScalar.size UScalarTy.U32 :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (show IScalar.toNat i7 ≤ 31 by omega)) hsz
    rw [hi8v, Nat.shiftLeft_eq, h1u, one_mul, Nat.mod_eq_of_lt hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hi6val, hi8val]
    have hle : (2 : Nat) ^ IScalar.toNat i7 ≤ 2 ^ 29 := Nat.pow_le_pow_right (by norm_num) hi7t
    omega
  · rw [hi6val]; exact (dvd_pow_self 2 (by omega : IScalar.toNat p.2 ≠ 0)).mul_left _
  · rw [hi8val]
    calc (2 : Nat) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ IScalar.toNat i7 := Nat.pow_le_pow_right (by norm_num) hi7t1
  · rw [hi8val]; exact dvd_pow_self 2 (by omega : IScalar.toNat i7 ≠ 0)

/-- On a tree index `xv = 2·xn` the `level` call returns `0`, so the `k+1` shift amount that
    `lowest_common_ancestor` compares is exactly `1` and shifting by it recovers the leaf index
    `xn`. This is what makes all early-return branches unreachable: both tests degenerate to
    `xn = yn`, which the precondition rules out. -/
theorem lca_level_one {xn : Nat} {xv : Std.U32} {k k1 : Std.Usize}
    (hxv : (↑xv : Nat) = xn * (↑(2#u32) : Nat))
    (hk : (↑k : Nat) ≤ 30 ∧ (↑xv : Nat) % 2 ^ ((↑k : Nat) + 1) = 2 ^ (↑k : Nat) - 1)
    (hk1 : (↑k1 : Nat) = ↑k + (↑(1#usize) : Nat)) :
    (↑k1 : Nat) = 1 ∧ (↑xv : Nat) >>> (↑k1 : Nat) = xn := by
  have h2 : (↑(2#u32) : Nat) = 2 := rfl
  have h1 : (↑(1#usize) : Nat) = 1 := rfl
  have hev : (↑xv : Nat) % 2 = 0 := by rw [hxv, h2]; omega
  have hk0 : (↑k : Nat) = 0 := level_res_eq_zero hev hk.2
  have hk1' : (↑k1 : Nat) = 1 := by rw [hk1, hk0, h1]
  refine ⟨hk1', ?_⟩
  rw [hk1', hxv, h2, Nat.shiftRight_eq_div_pow, pow_one]
  omega

end binary_tree.array_representation.treemath

/-! ### Pure companion specs (statements user-validated 2026-07-28) -/

/-- Pure membership-form companion of `direct_path.spec` (statement USER-VALIDATED 2026-07-28;
    the Rust spec may later gain clause 3 phrased via `level`).
    Clause 1-2 are the Rust post in membership form: at most 29 entries, every entry `valid`
    (`≤ 2^29 − 2 = MAX_PARENT`) and below `parent_count size = ↑size / 2`. Clause 3 is a
    positional strengthening needed by `copath`: the entry at position `i` is the level-`i+1`
    ancestor (`tones (2·e+1) = i+1`), so after `pop` no remaining entry can be the root.
    NOT `@[spec]`-registered while the proof is incomplete. -/
theorem binary_tree.array_representation.treemath.direct_path.spec_pure
    (node_index : binary_tree.array_representation.treemath.LeafNodeIndex)
    (size : binary_tree.array_representation.treemath.TreeSize)
    (h : (binary_tree.array_representation.treemath.direct_path.pre node_index size).holds) :
    ⦃ ⌜ True ⌝ ⦄
    binary_tree.array_representation.treemath.direct_path node_index size
    ⦃ ⇓ res => ⌜ vecLen res ≤ 29
        ∧ (∀ e ∈ res.1, (↑e : Nat) ≤ 2 ^ 29 - 2 ∧ (↑e : Nat) < (↑size : Nat) / 2)
        ∧ (∀ i, (hi : i < res.1.length) → tones (2 * (↑res.1[i] : Nat) + 1) = i + 1) ⌝ ⦄ := by
  sorry -- TODO(proof): from direct_path_loop_spec once repaired (lives in Proofs.lean)

end openmls
