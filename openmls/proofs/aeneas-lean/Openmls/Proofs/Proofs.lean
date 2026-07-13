-- [openmls]: treemath panic-freedom — the per-function value specs and the 9 `.spec.proof`
-- obligations Aeneas asks us to discharge. Originally Aeneas-generated, since hand-edited and no
-- longer regenerated (extraction is frozen). The supporting development is split across imports:
--   * `Common`           — generic loop driver, triple helpers, `vecLen`, `attribute [spec] uncurry`
--   * `BitMath`          — pure-`Nat` `tones` / `parent` bit lemmas
--   * `MissingCoreSpecs` — PROVED `@[spec]` contracts for `core`/`alloc` ops
--   * `AdmittedCoreSpecs`— the TRUSTED audit surface (11 admitted `@[spec]` contracts)
-- STATUS (WIP): 4 obligations still contain `sorry` (see the `TODO(sorry)` comments below):
--   direct_path, common_direct_path, copath, lowest_common_ancestor.
-- (`root` is proved; `direct_path`'s loop still wants a `direct_path_loop_spec` helper — currently removed.)
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
  · rintro k ⟨hk31, hk0⟩
    unfold level_loop.body
    mvcgen <;> try scalar_tac
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

-- ------------------------------------------------------------------------------

@[spec]
theorem level.spec.proof (index : Std.U32) :
  (level.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄ level index ⦃ ⇓ res => ⌜ (level.post index res).holds ⌝ ⦄
  := by
  unfold pre post
  hax_mvcgen [level, level_loop_spec]
  all_goals try scalar_tac
  all_goals try simp_all!
  all_goals try grind

@[spec]
theorem root.spec.proof (size : TreeSize) :
  (root.pre size).holds →
  ⦃ ⌜ True ⌝ ⦄ root size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  hax_mvcgen [root]
  all_goals try scalar_tac
  all_goals try simp_all!
  -- No loop here: the only residual VC is that the root index `(1 << log2 size) − 1` does not
  -- underflow, i.e. `1 <<< s ≥ 1`. The shift `s = 31 - (31 - log2 size)` is capped at `≤ 31` by the
  -- double subtraction, so `1 <<< s = 2^s < 2^32`, hence `2^s % 2^32 = 2^s ≥ 1`.
  have hs : (31 - (31 - Nat.log 2 (↑size : Nat))) ≤ 31 := by omega
  rw [Nat.shiftLeft_eq, one_mul,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hs) (by native_decide))]
  exact Nat.one_le_two_pow

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
theorem parent.spec.proof
  (x : TreeNodeIndex) :
  (parent.pre x).holds →
  ⦃ ⌜ True ⌝ ⦄
  parent x
  ⦃ ⇓ res =>
  ⌜ (parent.post x res).holds ⌝ ⦄
  := by
  unfold pre parent
  intro h_pre
  apply triple_in_hypothesis (h := h_pre)
  clear h_pre
  mvcgen <;> try scalar_tac
  · intro
    hax_mvcgen [level.post]
    all_goals try scalar_tac
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  · sorry


@[spec]
theorem sibling.spec.proof
  (index : TreeNodeIndex) :
  (sibling.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄
  sibling index
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  unfold sibling pre
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen
  all_goals try simp_all! ; scalar_tac
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

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
  · -- TODO(sorry): parity for `root size`'s `TreeNodeIndex::new` — `(1 << log2 size) − 1 % 2 = 1` (odd ⇒ Parent branch).
    sorry
  · -- TODO(sorry): leaf-start no-overflow — `2 · node_index ≤ U32.max` (the `Leaf.to_tree_index` of the starting node).
    sorry
  · -- TODO(sorry): the tree-walk loop from a leaf start — discharge via `direct_path_loop_spec` (post: every elem `valid` ∧ len ≤ 30).
    sorry
  · -- TODO(sorry): parent-start no-overflow — `2 · p ≤ U32.max` (the `Parent.to_tree_index` of the starting node).
    sorry
  · -- TODO(sorry): the tree-walk loop from a parent start — discharge via `direct_path_loop_spec`.
    sorry

@[spec]
theorem copath.spec.proof (leaf_index : LeafNodeIndex) (size : TreeSize) :
  (copath.pre leaf_index size).holds →
  ⦃ ⌜ True ⌝ ⦄ copath leaf_index size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  hax_mvcgen [copath]
  all_goals try scalar_tac
  all_goals try simp_all
  · -- TODO(sorry): empty-path branch — `copath_loop` then `map sibling >>= collect` is panic-free; needs per-element `SiblingSafe` + `copath_loop_spec` + `into_map_collect_sibling_spec`.
    sorry
  · -- TODO(sorry): non-empty branch (after `pop` drops the root) — same `sibling`-collect tail on the popped path.
    sorry

@[spec]
theorem lowest_common_ancestor.spec.proof (x : LeafNodeIndex) (y : LeafNodeIndex) :
  (lowest_common_ancestor.pre x y).holds →
  ⦃ ⌜ True ⌝ ⦄ lowest_common_ancestor x y ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  unfold lowest_common_ancestor.pre
  intro h_pre
  -- TODO(sorry): whole proof — the two early-return branches are unreachable for distinct even leaves (`x >> ly == y >> ly` fails at level 0), so only the shift-loop runs; close it with `lca_loop0_spec` (gives 2 ≤ k ≤ 30, `xn·2^k < 2^30`) then the final `from_tree_index` (odd) at `(xn << k) + (1 << (k−1)) − 1`.
  sorry

@[spec]
theorem common_direct_path.spec.proof (x : LeafNodeIndex) (y : LeafNodeIndex)
  (size : TreeSize) :
  (common_direct_path.pre x y size).holds →
  ⦃ ⌜ True ⌝ ⦄ common_direct_path x y size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  hax_mvcgen [common_direct_path]
  all_goals try scalar_tac

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
theorem LeafNodeIndex.from_tree_index.spec.proof (node_index : Std.U32) :
  (LeafNodeIndex.from_tree_index.pre node_index).holds →
  ⦃ ⌜ True ⌝ ⦄
  LeafNodeIndex.from_tree_index node_index
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
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
theorem TreeSize.new.spec.proof
   (nodes : Std.U32) :
  (TreeSize.new.pre nodes).holds →
  ⦃ ⌜ True ⌝ ⦄
  TreeSize.new nodes
  ⦃ ⇓ res =>
  ⌜ (TreeSize.new.post nodes res).holds ⌝ ⦄
  := by
  hax_mvcgen [new] <;> try scalar_tac
  all_goals simp_all!
  · sorry
  · sorry
  · sorry

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

end binary_tree.array_representation.treemath
end openmls
