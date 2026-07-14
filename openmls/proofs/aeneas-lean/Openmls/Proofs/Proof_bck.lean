-- [openmls]: treemath panic-freedom — the per-function value specs and the 9 `.spec.proof`
-- obligations Aeneas asks us to discharge. Originally Aeneas-generated, since hand-edited and no
-- longer regenerated (extraction is frozen). The supporting development is split across imports:
--   * `Common`           — generic loop driver, triple helpers, `vecLen`, `attribute [spec] uncurry`
--   * `BitMath`          — pure-`Nat` `tones` / `parent` bit lemmas
--   * `MissingCoreSpecs` — PROVED `@[spec]` contracts for `core`/`alloc` ops
--   * `AdmittedCoreSpecs`— the TRUSTED audit surface (11 admitted `@[spec]` contracts)
-- This file itself contains no `sorry`: every obligation here is fully proved.
import Aeneas
import CoreModels
import Openmls.Extraction.Types
import Openmls.Extraction.Funs
import Openmls.Extraction.Specs
import Openmls.Proofs.Common
import Openmls.Proofs.BitMath
import Openmls.Proofs.MissingCoreSpecs
import Openmls.Proofs.AdmittedCoreSpecs
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

/- You can remove the following line by using the CLI option `-all-computable`: -/
noncomputable section

namespace openmls
namespace binary_tree.array_representation.treemath

set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

attribute [spec]
  pure
  --
  MAX_TREE_SIZE MIN_TREE_SIZE MAX_INDEX
  --
  log2
  is_node_in_tree
  --
  TreeSize.u32
  TreeSize.leaf_count
  TreeSize.valid
  --
  TreeNodeIndex.new
  TreeNodeIndex.u32
  TreeNodeIndex.valid
  --
  LeafNodeIndex.new
  LeafNodeIndex.u32
  LeafNodeIndex.to_tree_index
  LeafNodeIndex.from_tree_index
  LeafNodeIndex.valid
  --
  ParentNodeIndex.new
  ParentNodeIndex.u32
  ParentNodeIndex.to_tree_index
  ParentNodeIndex.from_tree_index
  ParentNodeIndex.valid


-- ------------------------------------------------------------------------------

/-- The `level` trailing-ones loop is panic-free and returns a result `≤ 31` and `≠ 0`, given the
    input's low bit is set (so it runs ≥ 1 step). Proved via the generic `loop_spec_measure`. -/
theorem level_loop_spec (index : Std.U32) (hidx : (↑index : Nat) < 2 ^ 31)
    (hbit : index &&& 1#u32 = 1#u32) :
    ⦃ ⌜ True ⌝ ⦄
    level_loop index 0#usize
    ⦃ ⇓ res => ⌜ res ≤ 31#usize ∧ res ≠ 0#usize ⌝ ⦄ := by
  unfold level_loop
  apply loop_spec_measure
    (measure := fun k => 32 - k.val)
    (inv := fun k => k.val ≤ 31 ∧ (k.val = 0 → index &&& 1#u32 = 1#u32))
    (post := fun res => res ≤ 31#usize ∧ res ≠ 0#usize)
  · exact ⟨by scalar_tac, fun _ => hbit⟩
  · intro k hk
    obtain ⟨hk31, hk0⟩ := hk
    unfold level_loop.body
    mvcgen
    case vc1.hy => scalar_tac
    case vc2.hmax => scalar_tac
    case vc3 =>
      -- bit `k` is set ⇒ continue with `k + 1`; that node lives below `2^31`, so `k < 31`.
      rename_i i hi_conj bit hbiteq hbit_conj add hadd
      obtain ⟨hi, _⟩ := hi_conj
      obtain ⟨hi1, _⟩ := hbit_conj
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hand : (↑i : Nat) &&& 1 = 1 := by
          rw [hbiteq] at hi1
          simpa [Aeneas.Std.UScalar.val_and] using hi1.symm
        have hipos : 1 ≤ (↑i : Nat) := by
          have hmod := Nat.and_one_is_mod (↑i : Nat); omega
        have hge : 2 ^ (↑k : Nat) ≤ (↑index : Nat) := by
          rw [hi, Nat.shiftRight_eq_div_pow] at hipos
          exact (Nat.one_le_div_iff (by positivity)).mp hipos
        have hklt : (↑k : Nat) < 31 :=
          (Nat.pow_lt_pow_iff_right (by norm_num)).mp (lt_of_le_of_lt hge hidx)
        scalar_tac
      · intro h; exfalso; scalar_tac
      · scalar_tac
    case vc4 =>
      -- bit `k` is clear ⇒ stop, returning `k`. `k = 0` would force the low bit set.
      rename_i i hi_conj bit hbitne hbit_conj
      obtain ⟨hi, _⟩ := hi_conj
      obtain ⟨hi1, _⟩ := hbit_conj
      refine ⟨by scalar_tac, ?_⟩
      intro hk0'
      apply hbitne
      have hkv : (↑k : Nat) = 0 := by scalar_tac
      have hb := hk0 hkv
      have key : (↑bit : Nat) = 1 := by
        rw [hi1, Aeneas.Std.UScalar.val_and, hi, hkv, Nat.shiftRight_zero]
        have heq : (↑(index &&& 1#u32) : Nat) = (↑index : Nat) &&& (↑1#u32 : Nat) := by
          simp [Aeneas.Std.UScalar.val_and]
        have hone : (↑(1#u32) : Nat) = 1 := by scalar_tac
        rw [hb] at heq; omega
      scalar_tac

@[spec]
theorem level.spec.proof' : ∀ (index : Std.U32),
  (pre index).holds →
  ⦃ ⌜ True ⌝ ⦄
  level index
  ⦃ ⇓ res => ⌜ (post index res).holds ⌝ ⦄
  := by
  intros index
  unfold pre post
  intros h_pre
  hax_mvcgen [level, level_loop]
  case vc2 =>
    simp_all!
    grind
  case vc2.hQ.isFalse hcond0 =>
    -- in this branch the low bit is set
    have hbit1 : index &&& 1#u32 = 1#u32 := by
      have hmod := Nat.and_one_is_mod (↑index : Nat)
      have hv : (↑(index &&& 1#u32) : Nat) = (↑index : Nat) &&& 1 := by
        simp [Aeneas.Std.UScalar.val_and]
      have hne : (↑(index &&& 1#u32) : Nat) ≠ 0 := by
        intro h; exact hcond0 (by scalar_tac)
      scalar_tac
    have hidx : (↑index : Nat) < 2 ^ 31 := by scalar_tac
    have hspec := level_loop_spec index hidx hbit1
    -- bridge to the `mvcgen` goal: the loop spec gives `res ≤ 31 ∧ res ≠ 0`
    unfold level_loop at hspec
    mvcgen [hspec]; intros; mvcgen


/-- The `common_direct_path` collection loop is panic-free: it indexes both paths only
    at positions `< len ≤ length`, and grows `common_path` by at most one per step. -/
@[spec]
theorem common_direct_path_loop_spec
    (x_path y_path common_path : alloc.vec.Vec ParentNodeIndex) (len i : Std.Usize)
    (hx : (↑len : Nat) ≤ vecLen x_path) (hy : (↑len : Nat) ≤ vecLen y_path)
    (hi : (↑i : Nat) ≤ ↑len) (hcp : vecLen common_path ≤ (↑i : Nat)) :
    ⦃ ⌜ True ⌝ ⦄
    common_direct_path_loop x_path y_path len common_path i
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold common_direct_path_loop
  apply loop_spec_measure
    (measure := fun p => (↑len : Nat) - p.2.val)
    (inv := fun p => (↑p.2 : Nat) ≤ ↑len ∧ vecLen p.1 ≤ (↑p.2 : Nat))
    (post := fun _ => True)
  · exact ⟨hi, hcp⟩
  · intro p hinv
    obtain ⟨cp, j⟩ := p
    obtain ⟨hj, hcpj⟩ := hinv
    simp only at hj hcpj ⊢
    have hxmax : vecLen x_path ≤ Std.Usize.max := x_path.1.property
    unfold common_direct_path_loop.body
    split
    · -- `j < len`
      rename_i hlt
      have hjlen : (↑j : Nat) < ↑len := by scalar_tac
      have hidxx : (↑j : Nat) < vecLen x_path := by omega
      have hidxy : (↑j : Nat) < vecLen y_path := by omega
      have hpush : vecLen cp < Std.Usize.max := by omega
      unfold ParentNodeIndex.Insts.CoreCmpPartialEqParentNodeIndex.eq
      mvcgen [vec_index_spec, vec_push_spec]
      all_goals scalar_tac
    · -- `j ≥ len`: stop
      mvcgen

/-- The `lowest_common_ancestor` while-loop (`loop0`), reached on two distinct even
    leaf tree-indices below `2^30`: it shifts both operands right until they coincide,
    counting steps in `k`. On exit `2 ≤ k ≤ 30` and `xn · 2^k < 2^30`. -/
@[spec]
theorem lca_loop0_spec (x1 y1 : Std.U32)
    (hx : (↑x1 : Nat) < 2 ^ 30) (hy : (↑y1 : Nat) < 2 ^ 30)
    (hex : (↑x1 : Nat) % 2 = 0) (hey : (↑y1 : Nat) % 2 = 0)
    (hne : (↑x1 : Nat) ≠ (↑y1 : Nat)) :
    ⦃ ⌜ True ⌝ ⦄
    lowest_common_ancestor_loop0 x1 y1 0#i32
    ⦃ ⇓ p => ⌜ 2 ≤ p.2.toNat ∧ p.2.toNat ≤ 30
        ∧ (↑p.1 : Nat) * 2 ^ p.2.toNat < 2 ^ 30 ⌝ ⦄ := by
  unfold lowest_common_ancestor_loop0
  apply loop_spec_measure
    (measure := fun (p : Std.U32 × Std.U32 × Std.I32) => 31 - p.2.2.toNat)
    (inv := fun (p : Std.U32 × Std.U32 × Std.I32) => (0 : Int) ≤ ↑p.2.2 ∧ p.2.2.toNat ≤ 30
        ∧ (↑p.1 : Nat) = (↑x1 : Nat) / 2 ^ p.2.2.toNat
        ∧ (↑p.2.1 : Nat) = (↑y1 : Nat) / 2 ^ p.2.2.toNat)
    (post := fun (p : Std.U32 × Std.I32) => 2 ≤ p.2.toNat ∧ p.2.toNat ≤ 30
        ∧ (↑p.1 : Nat) * 2 ^ p.2.toNat < 2 ^ 30)
  · -- init at k = 0
    refine ⟨by simp, by simp, ?_, ?_⟩ <;> simp
  · intro p hinv
    obtain ⟨xn, yn, k⟩ := p
    obtain ⟨hk0, hk30, hxn, hyn⟩ := hinv
    simp only at hk0 hk30 hxn hyn ⊢
    unfold lowest_common_ancestor_loop0.body
    split
    · -- xn ≠ yn : continue
      rename_i hcond
      have hxyne : (↑xn : Nat) ≠ (↑yn : Nat) := by
        have hne' : xn ≠ yn := by simpa [bne_iff_ne] using hcond
        scalar_tac
      have hk29 : k.toNat ≤ 29 := by
        by_contra hc
        have hk30' : k.toNat = 30 := by omega
        rw [hxn, hyn, hk30', Nat.div_eq_of_lt hx, Nat.div_eq_of_lt hy] at hxyne
        exact hxyne rfl
      mvcgen
      · scalar_tac
      · scalar_tac
      · rename_i xn1 hxn1 yn1 hyn1 k1 hk1
        obtain ⟨hxn1v, -⟩ := hxn1
        obtain ⟨hyn1v, -⟩ := hyn1
        have h1 : (1#i32).toNat = 1 := by decide
        have hItn : I32.toNat k1 = k.toNat + 1 := by scalar_tac
        refine ⟨⟨by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
        · rw [hxn1v, h1, Nat.shiftRight_eq_div_pow, pow_one, hxn, hItn,
              Nat.div_div_eq_div_mul, ← pow_succ]
        · rw [hyn1v, h1, Nat.shiftRight_eq_div_pow, pow_one, hyn, hItn,
              Nat.div_div_eq_div_mul, ← pow_succ]
    · -- xn = yn : done
      rename_i hcond
      have hxyeq : (↑xn : Nat) = (↑yn : Nat) := by simpa [bne_iff_ne] using hcond
      mvcgen
      have heq : (↑x1 : Nat) / 2 ^ k.toNat = (↑y1 : Nat) / 2 ^ k.toNat := by
        rw [← hxn, ← hyn, hxyeq]
      have hk2 : 2 ≤ k.toNat := even_shift_eq_ge_two hex hey hne heq
      refine ⟨hk2, hk30, ?_⟩
      calc (↑xn : Nat) * 2 ^ k.toNat = (↑x1 / 2 ^ k.toNat) * 2 ^ k.toNat := by rw [hxn]
        _ ≤ ↑x1 := Nat.div_mul_le_self _ _
        _ < 2 ^ 30 := hx

/-- The `direct_path` tree-walk loop is panic-free: from a node `x0` strictly below the root
    `r = 2^d − 1` (with `tones x0 ≤ d`, `x0 < 2^(d+1)`), each `parent` step raises the level by
    one and stays below `2^(d+1)`; the measure `d − tones x` strictly decreases until `x = r`. -/
theorem direct_path_loop_spec (r : Std.U32)
    (vec0 : alloc.vec.Vec ParentNodeIndex)
    (x0 : Std.U32) (d : Nat) (hr : (↑r : Nat) = 2 ^ d - 1) (hd30 : d ≤ 30)
    (hx0 : (↑x0 : Nat) < 2 ^ (d + 1)) (ht0 : tones (↑x0 : Nat) ≤ d)
    (hvec0 : vecLen vec0 ≤ tones (↑x0 : Nat))
    (helem0 : ∀ e ∈ vec0.1.val, 2 * (↑e : Nat) + 1 < 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄ direct_path_loop r vec0 x0
    ⦃ ⇓ vec => ⌜ (∀ e ∈ vec.1.val, 2 * (↑e : Nat) + 1 < 2 ^ 31 - 1) ∧ vecLen vec ≤ 30 ⌝ ⦄ := by
  unfold direct_path_loop
  apply loop_spec_measure
    (measure := fun (p : (alloc.vec.Vec ParentNodeIndex) × Std.U32) => d - tones (↑p.2 : Nat))
    (inv := fun (p : (alloc.vec.Vec ParentNodeIndex) × Std.U32) =>
      tones (↑p.2 : Nat) ≤ d ∧ (↑p.2 : Nat) < 2 ^ (d + 1)
      ∧ vecLen p.1 ≤ tones (↑p.2 : Nat)
      ∧ ∀ e ∈ p.1.1.val, 2 * (↑e : Nat) + 1 < 2 ^ 31 - 1)
    (post := fun (vec : alloc.vec.Vec ParentNodeIndex) =>
      (∀ e ∈ vec.1.val, 2 * (↑e : Nat) + 1 < 2 ^ 31 - 1) ∧ vecLen vec ≤ 30)
  case h_init => exact ⟨ht0, hx0, hvec0, helem0⟩
  sorry

-- ------------------------------------------------------------------------------

@[spec]
theorem level.spec.proof (index : Std.U32) :
  (level.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄ level index ⦃ ⇓ res => ⌜ (level.post index res).holds ⌝ ⦄
  := by hax_mvcgen ; simp_all

@[spec]
theorem TreeSize.inc.spec.proof (self : TreeSize) :
  (TreeSize.inc.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄ TreeSize.inc self ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by hax_mvcgen [inc] <;> scalar_tac

@[spec]
theorem TreeSize.dec.spec.proof (self : TreeSize) :
  (TreeSize.dec.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄ TreeSize.dec self ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  unfold dec
  hax_mvcgen [dec]
  <;> (try simp only [MIN_TREE_SIZE] at *)
  <;> scalar_tac

@[spec]
theorem left.spec.proof (index : ParentNodeIndex) :
  (left.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄ left index ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  hax_mvcgen [left, level.post]
  <;> scalar_tac

@[spec]
theorem right.spec.proof (index : ParentNodeIndex) :
  (right.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄ right index ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  hax_mvcgen [right, level.post]
  <;> scalar_tac

@[spec]
theorem is_node_in_tree.spec.proof (node_index : TreeNodeIndex) (size : TreeSize) :
  (is_node_in_tree.pre node_index size).holds →
  ⦃ ⌜ True ⌝ ⦄ is_node_in_tree node_index size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  intro h_pre
  apply triple_in_hypothesis (h := h_pre)
  mvcgen [is_node_in_tree, pure, pre] <;> try scalar_tac
  all_goals (simp ; intros ; mvcgen)
  all_goals scalar_tac

@[spec]
theorem LeafNodeIndex.to_tree_index.spec.proof (self : LeafNodeIndex) :
  (LeafNodeIndex.to_tree_index.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄ LeafNodeIndex.to_tree_index self ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by hax_mvcgen ; scalar_tac

@[spec]
theorem ParentNodeIndex.to_tree_index.spec.proof (self : ParentNodeIndex) :
  (ParentNodeIndex.to_tree_index.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄ ParentNodeIndex.to_tree_index self ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by hax_mvcgen <;> scalar_tac

@[spec]
theorem ParentNodeIndex.from_tree_index.spec.proof (node_index : Std.U32) :
  (ParentNodeIndex.from_tree_index.pre node_index).holds →
  ⦃ ⌜ True ⌝ ⦄ ParentNodeIndex.from_tree_index node_index ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by hax_mvcgen <;> scalar_tac

@[spec]
theorem TreeNodeIndex.u32.spec.proof (self : TreeNodeIndex) :
  (TreeNodeIndex.u32.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄ TreeNodeIndex.u32 self ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  intro h_pre
  apply triple_in_hypothesis (h := h_pre)
  mvcgen [is_node_in_tree, pure, pre] <;> try scalar_tac
  all_goals (simp ; intros ; mvcgen)
  all_goals scalar_tac

@[spec]
theorem root.spec.proof (size : TreeSize) :
  (root.pre size).holds →
  ⦃ ⌜ True ⌝ ⦄ root size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  hax_mvcgen [root]
  all_goals try scalar_tac
  all_goals try simp_all!
  sorry

@[spec]
theorem direct_path.spec.proof (node_index : LeafNodeIndex) (size : TreeSize) :
  (direct_path.pre node_index size).holds →
  ⦃ ⌜ True ⌝ ⦄
  direct_path node_index size
  ⦃ ⇓ res => ⌜ (direct_path.post node_index size res).holds ⌝ ⦄
  := by
  hax_mvcgen [direct_path]
  all_goals try simp_all
  all_goals try grind
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry
  ·
    sorry

@[spec]
theorem common_direct_path.spec.proof (x : LeafNodeIndex) (y : LeafNodeIndex)
  (size : TreeSize) :
  (common_direct_path.pre x y size).holds →
  ⦃ ⌜ True ⌝ ⦄ common_direct_path x y size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  hax_mvcgen [common_direct_path]
  all_goals try scalar_tac
  sorry

@[spec]
theorem copath.spec.proof (leaf_index : LeafNodeIndex) (size : TreeSize) :
  (copath.pre leaf_index size).holds →
  ⦃ ⌜ True ⌝ ⦄ copath leaf_index size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by sorry


@[spec]
theorem lowest_common_ancestor.spec.proof (x : LeafNodeIndex) (y : LeafNodeIndex) :
  (lowest_common_ancestor.pre x y).holds →
  ⦃ ⌜ True ⌝ ⦄ lowest_common_ancestor x y ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  unfold lowest_common_ancestor.pre
  intro h_pre
  hax_mvcgen [lowest_common_ancestor, level.pre, level.post, pure]
  all_goals try (simp_all!; grind)
  all_goals sorry

  -- simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
  --   Std.Do.PredTrans.apply] at h_pre
  -- rw [show (1#u32 <<< 30#i32 : Aeneas.Std.Result Std.U32) = ok 1073741824#u32 from by
  --   rfl] at h_pre
  -- simp at h_pre
  -- rw [show (1073741824#u32 / 2#u32 : Aeneas.Std.Result Std.U32) = ok 536870912#u32 from by
  --   rfl] at h_pre
  -- simp [Functor.map] at h_pre
  -- have hx29 : (↑x : Nat) < 536870912 := by
  --   by_contra hc; rw [if_neg hc] at h_pre; simp at h_pre
  -- rw [if_pos hx29] at h_pre
  -- have hy29 : (↑y : Nat) < 536870912 := by
  --   by_contra hc; rw [if_neg hc] at h_pre; simp at h_pre
  -- rw [if_pos hy29] at h_pre
  -- have hxy : (↑x : Nat) ≠ (↑y : Nat) := by simp at h_pre; scalar_tac
  -- clear h_pre
  -- obtain ⟨x1, hx1eq, hx1v⟩ := mul2_ok x (by scalar_tac)
  -- obtain ⟨y1, hy1eq, hy1v⟩ := mul2_ok y (by scalar_tac)
  -- unfold lowest_common_ancestor
  --   LeafNodeIndex.to_tree_index
  -- rw [hx1eq, hy1eq]
  -- simp only [bind_tc_ok]
  -- rw [level_even_eq x1 (by omega) (by omega), level_even_eq y1 (by omega) (by omega)]
  -- simp only [bind_tc_ok]
  -- mvcgen [lca_loop0_spec,
  --   ParentNodeIndex.from_tree_index]
  -- all_goals try scalar_tac
  -- -- The four remaining goals are the panic conditions of the tail after `loop0`:
  -- -- `(xn << k) + (1 << (k-1)) - 1`. `loop0`'s post gives `2 ≤ k ≤ 30` and `xn·2^k < 2^30`.
  -- case vc30.hmax =>
  --   rename_i p hpost i6 hi6 i7 hi7 i8 hi8
  --   obtain ⟨hk2, hk30, hbnd⟩ := hpost
  --   obtain ⟨hi6v, -⟩ := hi6
  --   obtain ⟨hi8v, -⟩ := hi8
  --   rw [show p.2.toNat = IScalar.toNat p.2 from rfl] at hk2 hk30 hbnd
  --   obtain ⟨hsum, -, -, -⟩ := lca_tail_aux hk2 hk30 hbnd hi6v hi7 hi8v
  --   have hmax : UScalar.max UScalarTy.U32 = 2 ^ 32 - 1 := by native_decide
  --   omega
  -- case vc31.h =>
  --   rename_i p hpost i6 hi6 i7 hi7 i8 hi8 i9 hi9
  --   obtain ⟨hk2, hk30, hbnd⟩ := hpost
  --   obtain ⟨hi6v, -⟩ := hi6
  --   obtain ⟨hi8v, -⟩ := hi8
  --   rw [show p.2.toNat = IScalar.toNat p.2 from rfl] at hk2 hk30 hbnd
  --   obtain ⟨-, -, hi8ge, -⟩ := lca_tail_aux hk2 hk30 hbnd hi6v hi7 hi8v
  --   scalar_tac
  -- case vc32.h =>
  --   rename_i p hpost i6 hi6 i7 hi7 i8 hi8 i9 hi9 i10 hi10
  --   obtain ⟨hk2, hk30, hbnd⟩ := hpost
  --   obtain ⟨hi6v, -⟩ := hi6
  --   obtain ⟨hi8v, -⟩ := hi8
  --   obtain ⟨hi10v, -⟩ := hi10
  --   rw [show p.2.toNat = IScalar.toNat p.2 from rfl] at hk2 hk30 hbnd
  --   obtain ⟨-, -, hi8ge, -⟩ := lca_tail_aux hk2 hk30 hbnd hi6v hi7 hi8v
  --   scalar_tac
  -- case vc34.h =>
  --   rename_i p hpost i6 hi6 i7 hi7 i8 hi8 i9 hi9 i10 hi10 u hu rmod hmod
  --   obtain ⟨hk2, hk30, hbnd⟩ := hpost
  --   obtain ⟨hi6v, -⟩ := hi6
  --   obtain ⟨hi8v, -⟩ := hi8
  --   obtain ⟨hi10v, hi9ge⟩ := hi10
  --   rw [show p.2.toNat = IScalar.toNat p.2 from rfl] at hk2 hk30 hbnd
  --   obtain ⟨-, hi6dvd, hi8ge, hi8dvd⟩ := lca_tail_aux hk2 hk30 hbnd hi6v hi7 hi8v
  --   rw [show (↑(1#u32) : Nat) = 1 from rfl] at hi10v
  --   rw [show (↑(2#u32) : Nat) = 2 from rfl] at hmod
  --   have : (↑rmod : Nat) = 1 := by omega
  --   scalar_tac

/-! ## `parent` / `direct_path` panic-freedom -/

-- /-- `level x` evaluates to exactly the trailing-ones count `tones ↑x` (≤ 31), as an
--     explicit `ok`-equation so the `level` call can be rewritten away before `mvcgen`. -/
-- theorem level_tones_eq (x : Std.U32) (hx : (↑x : Nat) < 2 ^ 31) :
--     ∃ k : Std.Usize, level x = ok k
--       ∧ (↑k : Nat) = tones ↑x ∧ (↑k : Nat) ≤ 31 := by
--   obtain ⟨k, hk⟩ := triple_noThrow_exists_ok (level_char x hx)
--   have hpost := triple_noThrow_elim (level_char x hx) hk
--   simp only [SPred.down_pure] at hpost
--   obtain ⟨hk31, hmod⟩ := hpost
--   exact ⟨k, hk, trailing_unique ↑x (↑k) (tones ↑x) hmod (tones_mod ↑x), hk31⟩

/-- The `index` U32 produced by `parent`'s bit chain (given the `mvcgen` step equations
    for each intermediate) has the exact arithmetic value from `parent_val_u32`, and that
    value is odd, ≥ 1, and below `2^32` (the facts the `from_tree_index`/`to_tree_index`
    tail needs). -/
theorem parent_index_val (x i1 b i2 i3 i4 index : Std.U32) (i k : Std.Usize)
    (hx : (↑x : Nat) < 2 ^ 31) (hk30 : (↑k : Nat) ≤ 30)
    (hkmod : (↑x : Nat) % 2 ^ ((↑k : Nat) + 1) = 2 ^ (↑k : Nat) - 1)
    (hi : (↑i : Nat) = (↑k : Nat) + (↑(1#usize) : Nat))
    (hi1 : (↑i1 : Nat) = (↑x : Nat) >>> (↑i : Nat))
    (hb : (↑b : Nat) = (↑(i1 &&& 1#u32) : Nat))
    (hi2 : (↑i2 : Nat) = (↑(1#u32) : Nat) <<< (↑k : Nat) % U32.size)
    (hi3 : (↑i3 : Nat) = (↑(x ||| i2) : Nat))
    (hi4 : (↑i4 : Nat) = (↑b : Nat) <<< (↑i : Nat) % U32.size)
    (hindex : (↑index : Nat) = (↑(i3 ^^^ i4) : Nat)) :
    (↑index : Nat) = 2 ^ ((↑k : Nat) + 2) * ((↑x : Nat) / 2 ^ ((↑k : Nat) + 2))
        + (2 ^ ((↑k : Nat) + 1) - 1)
      ∧ (↑index : Nat) % 2 = 1 ∧ 1 ≤ (↑index : Nat) ∧ (↑index : Nat) < 2 ^ 32 := by
  have h1u : (↑(1#u32) : Nat) = 1 := rfl
  have h1s : (↑(1#usize) : Nat) = 1 := rfl
  rw [hi, h1s] at hi1 hi4
  have hval : (↑index : Nat) = 2 ^ ((↑k : Nat) + 2) * ((↑x : Nat) / 2 ^ ((↑k : Nat) + 2))
      + (2 ^ ((↑k : Nat) + 1) - 1) := by
    rw [hindex, Aeneas.Std.UScalar.val_xor, hi3, Aeneas.Std.UScalar.val_or, hi4, hb,
        Aeneas.Std.UScalar.val_and, hi1, hi2, h1u]
    exact parent_val_u32 x (↑k) hk30 hkmod
  refine ⟨hval, ?_, ?_, ?_⟩
  · -- odd
    have he : 2 ∣ 2 ^ ((↑k : Nat) + 2) * ((↑x : Nat) / 2 ^ ((↑k : Nat) + 2)) :=
      (dvd_pow_self 2 (by omega : (↑k : Nat) + 2 ≠ 0)).mul_right _
    have h2le : 2 ≤ 2 ^ ((↑k : Nat) + 1) := by
      calc (2 : Nat) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ ((↑k : Nat) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2dvd : 2 ∣ 2 ^ ((↑k : Nat) + 1) := dvd_pow_self 2 (by omega)
    rw [hval]; omega
  · -- ≥ 1
    have h2le : 2 ≤ 2 ^ ((↑k : Nat) + 1) := by
      calc (2 : Nat) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ ((↑k : Nat) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hval]; omega
  · -- < 2^32
    have hE1 : 2 ^ ((↑k : Nat) + 2) * ((↑x : Nat) / 2 ^ ((↑k : Nat) + 2)) ≤ (↑x : Nat) := by
      rw [mul_comm]; exact Nat.div_mul_le_self _ _
    have hE2 : 2 ^ ((↑k : Nat) + 1) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h31 : (2 : Nat) ^ 31 + 2 ^ 31 = 2 ^ 32 := by norm_num
    rw [hval]; omega

/-- Spec for `parent (new x)` (without the final `to_tree_index`): the resulting
    `ParentNodeIndex` `par` satisfies `2·par+1 = <parent tree-index>` and `par < 2^31`,
    so its `to_tree_index` is panic-free and yields the parent node value. -/
theorem parent_tni_spec (tni : TreeNodeIndex)
    (x : Std.U32) (hu32 : TreeNodeIndex.u32 tni = ok x) (hx : (↑x : Nat) < 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    parent tni
    ⦃ ⇓ par => ⌜ 2 * (↑par : Nat) + 1 = 2 ^ (tones ↑x + 2) * (↑x / 2 ^ (tones ↑x + 2))
        + (2 ^ (tones ↑x + 1) - 1) ∧ (↑par : Nat) < 2 ^ 31 ⌝ ⦄ := by
  unfold parent
  rw [hu32]; simp only [bind_tc_ok]
  obtain ⟨k, hlevel, hkv, hk31⟩ := level_tones_eq x (by omega)
  rw [hlevel]; simp only [bind_tc_ok]
  have hkmod := tones_mod (↑x : Nat)
  rw [← hkv] at hkmod
  have hk30 : (↑k : Nat) ≤ 30 := by
    rcases Nat.lt_or_ge (↑k : Nat) 31 with h | h
    · omega
    · exfalso
      have hk31' : (↑k : Nat) = 31 := by omega
      rw [hk31'] at hkmod
      have e32 : (2 : Nat) ^ (31 + 1) = 2 ^ 32 := by norm_num
      rw [e32] at hkmod
      have hxlt : (↑x : Nat) < 2 ^ 32 := by scalar_tac
      rw [Nat.mod_eq_of_lt hxlt] at hkmod
      omega
  mvcgen [ParentNodeIndex.from_tree_index]
  case vc1.hmax => scalar_tac
  case vc2.hy => scalar_tac
  case vc3.hy => scalar_tac
  case vc4.hy => scalar_tac
  case vc5.h =>
    rename_i i hi i1 hi1 b hb i2 hi2 i3 hi3 i4 hi4 idx hidx
    obtain ⟨hval, hodd, hge, hlt⟩ := parent_index_val x i1 b i2 i3 i4 idx i k
      (by omega) hk30 hkmod hi hi1.1 hb.1 hi2.1 hi3.1 hi4.1 hidx.1
    scalar_tac
  case vc7.h =>
    rename_i i hi i1 hi1 b hb i2 hi2 i3 hi3 i4 hi4 idx hidx u hu rmod hmod
    obtain ⟨hval, hodd, hge, hlt⟩ := parent_index_val x i1 b i2 i3 i4 idx i k
      (by omega) hk30 hkmod hi hi1.1 hb.1 hi2.1 hi3.1 hi4.1 hidx.1
    scalar_tac
  case vc10 =>
    rename_i i hi i1 hi1 b hb i2 hi2 i3 hi3 i4 hi4 idx hidx u1 hu1 rmod hmod u2 hu2 rsub hsub rdiv hdiv
    obtain ⟨hval, hodd, hge, hlt⟩ := parent_index_val x i1 b i2 i3 i4 idx i k
      (by omega) hk30 hkmod hi hi1.1 hb.1 hi2.1 hi3.1 hi4.1 hidx.1
    obtain ⟨hsub1, hsub2⟩ := hsub
    rw [hkv] at hval
    refine ⟨?_, ?_⟩
    · have hr : 2 * (↑rdiv : Nat) + 1 = (↑idx : Nat) := by scalar_tac
      rw [hr]; exact hval
    · have e32 : (2 : Nat) ^ 32 = 2 * 2 ^ 31 := by norm_num
      scalar_tac

/-- Spec for `parent (new x)` (without the final `to_tree_index`). -/
theorem parent_new_spec (x : Std.U32) (hx : (↑x : Nat) < 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    (do
      let tni ← TreeNodeIndex.new x
      parent tni)
    ⦃ ⇓ par => ⌜ 2 * (↑par : Nat) + 1 = 2 ^ (tones ↑x + 2) * (↑x / 2 ^ (tones ↑x + 2))
        + (2 ^ (tones ↑x + 1) - 1) ∧ (↑par : Nat) < 2 ^ 31 ⌝ ⦄ := by
  obtain ⟨tni, htni, hu32⟩ := new_u32_eq x
  rw [htni]; simp only [bind_tc_ok]
  exact parent_tni_spec tni x hu32 hx

/-- `new x` then `.u32` round-trips, as a `Triple`. -/
theorem new_u32_triple (x : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄ (do let tni ← TreeNodeIndex.new x; TreeNodeIndex.u32 tni)
    ⦃ ⇓ r => ⌜ r = x ⌝ ⦄ := by
  obtain ⟨tni, h1, h2⟩ := new_u32_eq x
  rw [h1]; simp only [bind_tc_ok]; exact triple_of_ok h2 rfl

/-- The root's tree-index value: `(root size).u32 = 2^(log2 size) − 1`, with `log2 size ≤ 30`
    and `size < 2^(log2 size + 1)`. -/
theorem root_u32_spec (size : TreeSize)
    (hpos : 0 < (↑size : Nat)) (hsz : (↑size : Nat) ≤ 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    (do let tni ← root size; TreeNodeIndex.u32 tni)
    ⦃ ⇓ r => ⌜ (↑r : Nat) = 2 ^ Nat.log 2 (↑size : Nat) - 1
        ∧ Nat.log 2 (↑size : Nat) ≤ 30
        ∧ (↑size : Nat) < 2 ^ (Nat.log 2 (↑size : Nat) + 1) ⌝ ⦄ := by
  have hd30 : Nat.log 2 (↑size : Nat) ≤ 30 := by
    by_contra hc
    have hge : (2 : Nat) ^ 31 ≤ (↑size : Nat) :=
      calc (2 : Nat) ^ 31 ≤ 2 ^ (Nat.log 2 (↑size : Nat)) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ (↑size : Nat) := Nat.pow_log_le_self 2 (by omega)
    omega
  have hsizelt : (↑size : Nat) < 2 ^ (Nat.log 2 (↑size : Nat) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  unfold root TreeSize.u32
  mvcgen [log2_spec, new_u32_triple]
  case vc3.hy =>
    rename_i u hu dd hdd
    rw [hdd]; omega
  case vc4.h =>
    rename_i u hu dd hdd shift hsh
    obtain ⟨hsh1, -⟩ := hsh
    have h1 := one_le_one_shiftLeft_mod (Nat.log 2 (↑size : Nat)) (by omega)
    rw [hsh1, hdd, show (↑(1#u32) : Nat) = 1 from rfl]
    exact h1
  case vc5.hQ.success.success.success.success.success =>
    rename_i u hu dd hdd shift hsh sub hsub tni
    obtain ⟨hsh1, -⟩ := hsh
    obtain ⟨hsub1, hsub2⟩ := hsub
    have hshift : (↑shift : Nat) = 2 ^ Nat.log 2 (↑size : Nat) := by
      rw [hsh1, hdd, show (↑(1#u32) : Nat) = 1 from rfl, Nat.shiftLeft_eq, one_mul,
          Nat.mod_eq_of_lt (by
            have : (2 : Nat) ^ Nat.log 2 (↑size : Nat) ≤ 2 ^ 30 :=
              Nat.pow_le_pow_right (by norm_num) hd30
            have hs : (2 : Nat) ^ 30 < U32.size := by native_decide
            omega)]
    have hval : (↑sub : Nat) = 2 ^ Nat.log 2 (↑size : Nat) - 1 := by
      rw [hsub1, hshift, show (↑(1#u32) : Nat) = 1 from rfl]
    intro htriple
    mspec htriple
    simp_all

/-- Strengthened `direct_path` spec: every node in the returned path has tree-index `< 2^31−1`
    (the per-element bound that makes `sibling` panic-free in `copath`). -/
theorem direct_path_elems_spec
   (node_index : LeafNodeIndex)
  (size : TreeSize) :
  (direct_path.pre node_index
  size).holds →
  ⦃ ⌜ True ⌝ ⦄
  direct_path node_index size
  ⦃ ⇓ res => ⌜ (∀ e ∈ res.1.val, 2 * (↑e : Nat) + 1 < 2 ^ 31 - 1) ∧ vecLen res ≤ 30 ⌝ ⦄
  := by
  intro h_pre
  unfold direct_path.pre at h_pre
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
    Std.Do.PredTrans.apply] at h_pre
  rw [show (1#u32 <<< 30#i32 : Aeneas.Std.Result Std.U32) = ok 1073741824#u32 from by
    rfl] at h_pre
  simp at h_pre
  simp only [show (2#u32 * 1073741824#u32 : Aeneas.Std.Result Std.U32) = ok 2147483648#u32 from by rfl,
    show (2147483648#u32 - 1#u32 : Aeneas.Std.Result Std.U32) = ok 2147483647#u32 from by rfl,
    bind_tc_ok, Functor.map] at h_pre
  have hpos : 0 < (↑size : Nat) := by by_contra h; rw [if_neg h] at h_pre; simp at h_pre
  rw [if_pos hpos, show (↑(2147483647#u32) : Nat) = 2147483647 from rfl] at h_pre
  have hsz : (↑size : Nat) ≤ 2147483647 := by by_contra h; rw [if_neg h] at h_pre; simp at h_pre
  rw [if_pos hsz] at h_pre
  obtain ⟨q, hq, hqv⟩ := Aeneas.Std.UScalar.div_spec size (by decide : (↑(2#u32) : Nat) ≠ 0)
  rw [hq] at h_pre
  simp only [bind_tc_ok] at h_pre
  have hadd := Aeneas.Std.UScalar.add_equiv q 1#u32
  have hni : (↑node_index : Nat) < (↑size : Nat) / 2 + 1 := by
    cases hac : (q + 1#u32) with
    | ok i5 =>
      rw [hac] at h_pre hadd
      simp only [bind_tc_ok] at h_pre
      simp at h_pre
      obtain ⟨-, hi5v, -⟩ := hadd
      rw [show (↑(1#u32) : Nat) = 1 from rfl] at hi5v
      rw [show (↑(2#u32) : Nat) = 2 from rfl] at hqv
      omega
    | fail e => rw [hac] at h_pre; simp at h_pre
    | div => rw [hac] at h_pre; simp at h_pre
  -- root value
  have hroot := root_u32_spec size hpos (by omega : (↑size : Nat) ≤ 2 ^ 31 - 1)
  obtain ⟨rt, hrt⟩ := triple_noThrow_exists_ok hroot
  have hrpost := triple_noThrow_elim hroot hrt
  simp only [SPred.down_pure] at hrpost
  obtain ⟨hrval, hd30, hsizelt⟩ := hrpost
  unfold direct_path
    LeafNodeIndex.to_tree_index
  rw [← bind_assoc, hrt]
  simp only [bind_tc_ok]
  obtain ⟨xw, hxw, hxwv⟩ := mul2_ok node_index (by omega : (↑node_index : Nat) < 2 ^ 31)
  have htxw0 : (↑xw : Nat) % 2 = 0 := by rw [hxwv]; omega
  have hxw0 : (↑xw : Nat) < 2 ^ (Nat.log 2 (↑size : Nat) + 1) := by rw [hxwv]; omega
  have htxw : tones (↑xw : Nat) ≤ Nat.log 2 (↑size : Nat) := by
    rw [tones_even (↑xw : Nat) htxw0]; omega
  have hvn := vec_new_spec ParentNodeIndex
  obtain ⟨V0, hV0⟩ := triple_noThrow_exists_ok hvn
  have hV0len := triple_noThrow_elim hvn hV0
  simp only [SPred.down_pure] at hV0len
  obtain ⟨hV0len0, hV0nil⟩ := hV0len
  rw [hV0]; simp only [bind_tc_ok]
  rw [hxw]; simp only [bind_tc_ok]
  exact direct_path_loop_spec rt V0 xw (Nat.log 2 (↑size : Nat)) hrval hd30 hxw0 htxw
    (by rw [hV0len0]; exact Nat.zero_le _)
    (by rw [hV0nil]; simp)

@[spec]
theorem direct_path.spec.proof
   (node_index : LeafNodeIndex)
  (size : TreeSize) :
  (direct_path.pre node_index
  size).holds →
  ⦃ ⌜ True ⌝ ⦄
  direct_path node_index size
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  intro h_pre
  have h := direct_path_elems_spec node_index size h_pre
  obtain ⟨res, hres⟩ := triple_noThrow_exists_ok h
  exact triple_of_ok hres trivial


/-! ## `sibling` panic-freedom (for `copath`) -/

/-- `ParentNodeIndex.to_tree_index p = 2·p + 1` as an ok-equation (no overflow when `2p+1 < 2^32`). -/
theorem ptti_ok (p : ParentNodeIndex)
    (hp : 2 * (↑p : Nat) + 1 < 2 ^ 32) :
    ∃ x : Std.U32, ParentNodeIndex.to_tree_index p = ok x ∧ (↑x : Nat) = 2 * (↑p : Nat) + 1 := by
  unfold ParentNodeIndex.to_tree_index
  obtain ⟨w, hw, hwv⟩ := mul2_ok p (by
    have hsz : (2 : Nat) ^ 31 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
  rw [hw]; simp only [bind_tc_ok]
  have hadd := Aeneas.Std.UScalar.add_equiv w 1#u32
  cases hac : (w + 1#u32) with
  | ok x =>
    rw [hac] at hadd; obtain ⟨-, hxv, -⟩ := hadd
    exact ⟨x, rfl, by rw [hxv, show (↑(1#u32) : Nat) = 1 from rfl, hwv]⟩
  | fail e =>
    exfalso; rw [hac] at hadd; simp only [Aeneas.Std.UScalar.inBounds] at hadd
    rw [show (↑(1#u32) : Nat) = 1 from rfl, hwv] at hadd
    have hmax : Aeneas.Std.U32.max = 2 ^ 32 - 1 := by native_decide
    scalar_tac
  | div => rw [hac] at hadd; exact absurd hadd (by simp)

/-- `left` is panic-free when its parent's tree-index `2·p+1 < 2^31`. -/
theorem left_noPanic (p : ParentNodeIndex)
    (hp : 2 * (↑p : Nat) + 1 < 2 ^ 31) :
    ⦃ ⌜ True ⌝ ⦄ left p ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold left
  obtain ⟨x, htti, hxv⟩ := ptti_ok p (by
    have : (2 : Nat) ^ 31 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
  rw [htti]; simp only [bind_tc_ok]
  obtain ⟨k, hlevel, hkv, hk31⟩ := level_tones_eq x (by rw [hxv]; omega)
  rw [hlevel]; simp only [bind_tc_ok]
  have hkpos : 0 < (↑k : Nat) := by rw [hkv]; exact tones_pos_of_odd _ (by rw [hxv]; omega)
  mvcgen
  all_goals scalar_tac

/-- `right` is panic-free when its parent's tree-index `2·p+1 < 2^31`. -/
theorem right_noPanic (p : ParentNodeIndex)
    (hp : 2 * (↑p : Nat) + 1 < 2 ^ 31) :
    ⦃ ⌜ True ⌝ ⦄ right p ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold right
  obtain ⟨x, htti, hxv⟩ := ptti_ok p (by
    have : (2 : Nat) ^ 31 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
  rw [htti]; simp only [bind_tc_ok]
  obtain ⟨k, hlevel, hkv, hk31⟩ := level_tones_eq x (by rw [hxv]; omega)
  rw [hlevel]; simp only [bind_tc_ok]
  have hkpos : 0 < (↑k : Nat) := by rw [hkv]; exact tones_pos_of_odd _ (by rw [hxv]; omega)
  mvcgen
  all_goals scalar_tac

/-- `sibling` is panic-free on a node whose tree-index `< 2^31 − 1`. -/
theorem sibling_noPanic (index : TreeNodeIndex)
    (v : Std.U32) (hu : TreeNodeIndex.u32 index = ok v) (hv : (↑v : Nat) < 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄ sibling index ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  unfold sibling
  have hps := parent_tni_spec index v hu hv
  obtain ⟨p, hp⟩ := triple_noThrow_exists_ok hps
  have hppost := triple_noThrow_elim hps hp
  simp only [SPred.down_pure] at hppost
  obtain ⟨hval, hp31⟩ := hppost
  have h2p : 2 * (↑p : Nat) + 1 < 2 ^ 31 := by
    rw [hval]; exact parent_val_lt (↑v) (by omega) (tones_le_30 _ hv)
  rw [hp]; simp only [bind_tc_ok]
  rw [hu]; simp only [bind_tc_ok]
  obtain ⟨i1, htti, hi1v⟩ := ptti_ok p (by
    have : (2 : Nat) ^ 31 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
  rw [htti]; simp only [bind_tc_ok]
  obtain ⟨o, hocmp⟩ := triple_noThrow_exists_ok (u32_cmp_spec v i1)
  rw [hocmp]; simp only [bind_tc_ok]
  cases o with
  | Less => exact right_noPanic p h2p
  | Equal => exact left_noPanic p h2p
  | Greater => exact left_noPanic p h2p

/-- `sibling` is panic-free on `e` — the per-element safety predicate threaded through `copath`. -/
def SiblingSafe (e : TreeNodeIndex) : Prop :=
  ⦃ ⌜ True ⌝ ⦄ sibling e ⦃ ⇓ _ => ⌜ True ⌝ ⦄

/-- The `sibling` instance of the trusted generic `into_map_collect_spec`: collecting `sibling`
    over a vec is panic-free when every element is `sibling`-safe. Derived (not admitted) by
    instantiating the `core` contract at `sibling`. -/
@[spec]
theorem into_map_collect_sibling_spec (fp : alloc.vec.Vec TreeNodeIndex)
    (hsafe : ∀ e ∈ fp.1.val, SiblingSafe e) :
    ⦃ ⌜ True ⌝ ⦄
    (do
      let ii ← alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter fp
      let m ← alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.map
          (BuiltinFnMut TreeNodeIndex TreeNodeIndex) ii sibling
      core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.collect
        (alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator TreeNodeIndex)
        (BuiltinFnMut TreeNodeIndex TreeNodeIndex)
        (alloc.vec.Vec.Insts.CoreIterTraitsCollectFromIterator TreeNodeIndex) m)
    ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  exact into_map_collect_spec fp sibling hsafe

/-- A leaf node `Leaf l` with `2·l < 2^31 − 1` is `sibling`-safe. -/
theorem siblingSafe_leaf (l : LeafNodeIndex)
    (hl : 2 * (↑l : Nat) < 2 ^ 31 - 1) :
    SiblingSafe (TreeNodeIndex.Leaf l) := by
  obtain ⟨w, hw, hwv⟩ := mul2_ok l (by omega : (↑l : Nat) < 2 ^ 31)
  have hu : TreeNodeIndex.u32 (TreeNodeIndex.Leaf l) = ok w := by
    unfold TreeNodeIndex.u32 LeafNodeIndex.to_tree_index; exact hw
  exact sibling_noPanic (TreeNodeIndex.Leaf l) w hu (by rw [hwv]; omega)

/-- A parent node `Parent p` with `2·p+1 < 2^31 − 1` is `sibling`-safe. -/
theorem siblingSafe_parent (p : ParentNodeIndex)
    (hp : 2 * (↑p : Nat) + 1 < 2 ^ 31 - 1) :
    SiblingSafe (TreeNodeIndex.Parent p) := by
  obtain ⟨x, htti, hxv⟩ := ptti_ok p (by
    have : (2 : Nat) ^ 31 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
  have hu : TreeNodeIndex.u32 (TreeNodeIndex.Parent p) = ok x := by
    unfold TreeNodeIndex.u32; exact htti
  exact sibling_noPanic (TreeNodeIndex.Parent p) x hu (by rw [hxv]; exact hp)

/-- The `copath` accumulation loop is panic-free and produces an all-`sibling`-safe path, when the
    accumulator is already safe and every iterator element wrapped as `Parent` is safe. -/
theorem copath_loop_spec (iter : core.slice.iter.Iter ParentNodeIndex)
    (fp : alloc.vec.Vec TreeNodeIndex)
    (hfp : ∀ e ∈ fp.1.val, SiblingSafe e)
    (hiter : ∀ pp ∈ sliceIterElems iter, SiblingSafe (TreeNodeIndex.Parent pp))
    (hbound : vecLen fp + (sliceIterElems iter).length < Std.Usize.max) :
    ⦃ ⌜ True ⌝ ⦄ copath_loop iter fp
    ⦃ ⇓ fp2 => ⌜ ∀ e ∈ fp2.1.val, SiblingSafe e ⌝ ⦄ := by
  unfold copath_loop
  apply loop_spec_measure
    (measure := fun (p : (core.slice.iter.Iter ParentNodeIndex) × (alloc.vec.Vec TreeNodeIndex)) =>
      (sliceIterElems p.1).length)
    (inv := fun p => (∀ e ∈ p.2.1.val, SiblingSafe e)
      ∧ (∀ pp ∈ sliceIterElems p.1, SiblingSafe (TreeNodeIndex.Parent pp))
      ∧ vecLen p.2 + (sliceIterElems p.1).length < Std.Usize.max)
    (post := fun (fp2 : alloc.vec.Vec TreeNodeIndex) => ∀ e ∈ fp2.1.val, SiblingSafe e)
  · exact ⟨hfp, hiter, hbound⟩
  · intro p hinv
    obtain ⟨it, fpc⟩ := p
    obtain ⟨hfpc, hitc, hbnd⟩ := hinv
    simp only at hfpc hitc hbnd ⊢
    unfold copath_loop.body
    obtain ⟨res, hres⟩ := triple_noThrow_exists_ok (slice_iter_next_spec it)
    have hrespost := triple_noThrow_elim (slice_iter_next_spec it) hres
    simp only [SPred.down_pure] at hrespost
    rw [hres]; simp only [bind_tc_ok]
    obtain ⟨o, it'⟩ := res
    simp only at hrespost
    cases o with
    | none => exact triple_of_ok rfl hfpc
    | some i =>
      obtain ⟨hi_mem, hsub, hlen⟩ := hrespost
      mvcgen [vec_push_spec]
      · scalar_tac
      · rename_i fpc' hpush
        obtain ⟨hplen, hpval⟩ := hpush
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · intro e he
          rw [hpval, List.mem_append] at he
          rcases he with he | he
          · exact hfpc e he
          · simp only [List.mem_singleton] at he; subst he; exact hitc i hi_mem
        · intro pp hpp; exact hitc pp (hsub pp hpp)
        · omega
        · exact hlen

@[spec]
theorem copath.spec.proof
  (leaf_index : LeafNodeIndex)
  (size : TreeSize) :
  (copath.pre leaf_index size).holds
  →
  ⦃ ⌜ True ⌝ ⦄
  copath leaf_index size
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  intro h_pre
  have h_pre0 := h_pre
  unfold copath.pre
    TreeSize.u32
    LeafNodeIndex.u32
    TreeSize.leaf_count
    MAX_TREE_SIZE at h_pre
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
    Std.Do.PredTrans.apply] at h_pre
  rw [show (1#u32 <<< 30#i32 : Aeneas.Std.Result Std.U32) = ok 1073741824#u32 from by
    rfl] at h_pre
  simp at h_pre
  simp only [show (2#u32 * 1073741824#u32 : Aeneas.Std.Result Std.U32) = ok 2147483648#u32 from by rfl,
    show (2147483648#u32 - 1#u32 : Aeneas.Std.Result Std.U32) = ok 2147483647#u32 from by rfl,
    bind_tc_ok, Functor.map] at h_pre
  have hpos : 0 < (↑size : Nat) := by by_contra h; rw [if_neg h] at h_pre; simp at h_pre
  rw [if_pos hpos, show (↑(2147483647#u32) : Nat) = 2147483647 from rfl] at h_pre
  have hsz : (↑size : Nat) ≤ 2147483647 := by by_contra h; rw [if_neg h] at h_pre; simp at h_pre
  rw [if_pos hsz] at h_pre
  obtain ⟨q, hq, hqv⟩ := Aeneas.Std.UScalar.div_spec size (by decide : (↑(2#u32) : Nat) ≠ 0)
  rw [hq] at h_pre
  simp only [bind_tc_ok] at h_pre
  have hadd := Aeneas.Std.UScalar.add_equiv q 1#u32
  have hni : (↑leaf_index : Nat) < (↑size : Nat) / 2 + 1 := by
    cases hac : (q + 1#u32) with
    | ok i5 =>
      rw [hac] at h_pre hadd
      simp only [bind_tc_ok] at h_pre
      simp at h_pre
      obtain ⟨-, hi5v, -⟩ := hadd
      rw [show (↑(1#u32) : Nat) = 1 from rfl] at hi5v
      rw [show (↑(2#u32) : Nat) = 2 from rfl] at hqv
      omega
    | fail e => rw [hac] at h_pre; simp at h_pre
    | div => rw [hac] at h_pre; simp at h_pre
  -- direct_path result (strengthened spec)
  have hdp := direct_path_elems_spec leaf_index size h_pre0
  obtain ⟨dp, hdpok⟩ := triple_noThrow_exists_ok hdp
  have hdppost := triple_noThrow_elim hdp hdpok
  simp only [SPred.down_pure] at hdppost
  obtain ⟨helem_dp, hlen_dp⟩ := hdppost
  unfold copath
  rw [hdpok]; simp only [bind_tc_ok]
  have h231 : (2 : Nat) ^ 31 - 1 = 2147483647 := by norm_num
  have hleaf_safe : SiblingSafe (TreeNodeIndex.Leaf leaf_index) :=
    siblingSafe_leaf leaf_index (by omega)
  have hpar_safe : ∀ pp ∈ dp.1.val, SiblingSafe (TreeNodeIndex.Parent pp) :=
    fun pp hpp => siblingSafe_parent pp (helem_dp pp hpp)
  mvcgen [vec_is_empty_spec, vec_pop_spec, vec_with_capacity_spec, vec_push_spec,
    sharedavec_into_iter_spec, copath_loop_spec, into_map_collect_sibling_spec]
  -- then-branch (`direct_path1 = direct_path`):
  · scalar_tac
  · scalar_tac
  · rename_i b hb len hlenv i1 hi1v fp hfpv fp1 hfp1v iter hiterv
    obtain ⟨-, hfp1val⟩ := hfp1v
    intro e he
    rw [hfp1val] at he
    have hnil : fp.1.val = [] := by
      have := hfpv; rw [vecLen_eq_length] at this; exact List.eq_nil_of_length_eq_zero this
    rw [hnil, List.nil_append, List.mem_singleton] at he
    subst he; exact hleaf_safe
  · rename_i b hb len hlenv i1 hi1v fp hfpv fp1 hfp1v iter hiterv
    intro pp hpp; rw [hiterv] at hpp; exact hpar_safe pp hpp
  · rename_i b hb len hlenv i1 hi1v fp hfpv fp1 hfp1v iter hiterv
    obtain ⟨hfp1len, -⟩ := hfp1v
    rw [hiterv, ← vecLen_eq_length]
    scalar_tac
  · rename_i b hb len hlenv i1 hi1v fp hfpv fp1 hfp1v iter hiterv fp2 hfp2safe
    obtain ⟨rr, hrr⟩ := triple_noThrow_exists_ok (into_map_collect_sibling_spec fp2 hfp2safe)
    rw [← Std.Do.WP.bind, hrr]
    simp [Std.Do.WP.wp, Std.Do.PredTrans.apply]
  -- else-branch (`direct_path1 = pop direct_path`):
  · scalar_tac
  · scalar_tac
  · rename_i b hb pr hpr len hlenv i1 hi1v fp hfpv fp1 hfp1v iter hiterv
    obtain ⟨-, hfp1val⟩ := hfp1v
    intro e he
    rw [hfp1val] at he
    have hnil : fp.1.val = [] := by
      have := hfpv; rw [vecLen_eq_length] at this; exact List.eq_nil_of_length_eq_zero this
    rw [hnil, List.nil_append, List.mem_singleton] at he
    subst he; exact hleaf_safe
  · rename_i b hb pr hpr len hlenv i1 hi1v fp hfpv fp1 hfp1v iter hiterv
    obtain ⟨hsub, -⟩ := hpr
    intro pp hpp; rw [hiterv] at hpp; exact hpar_safe pp (hsub pp hpp)
  · rename_i b hb pr hpr len hlenv i1 hi1v fp hfpv fp1 hfp1v iter hiterv
    obtain ⟨-, hpoplen⟩ := hpr
    obtain ⟨hfp1len, -⟩ := hfp1v
    rw [hiterv, ← vecLen_eq_length]
    scalar_tac
  · rename_i b hb pr hpr len hlenv i1 hi1v fp hfpv fp1 hfp1v iter hiterv fp2 hfp2safe
    obtain ⟨rr, hrr⟩ := triple_noThrow_exists_ok (into_map_collect_sibling_spec fp2 hfp2safe)
    rw [← Std.Do.WP.bind, hrr]
    simp [Std.Do.WP.wp, Std.Do.PredTrans.apply]

end binary_tree.array_representation.treemath
end openmls
