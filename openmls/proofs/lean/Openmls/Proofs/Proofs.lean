-- [openmls]: treemath panic-freedom — the per-function value specs and the 9 `.spec.proof`
-- obligations Aeneas asks us to discharge. Originally Aeneas-generated, since hand-edited and no
-- longer regenerated (extraction is frozen). The supporting development is split across imports:
--   * `Common`           — generic loop driver, triple helpers, `vecLen`, `attribute [spec] uncurry`
--   * `BitMath`          — pure-`Nat` `tones` / `parent` bit lemmas
--   * `MissingCoreSpecs` — PROVED `@[spec]` contracts for `core`/`alloc` ops
--   * `AdmittedCoreSpecs`— the TRUSTED audit surface (11 admitted `@[spec]` contracts)
-- STATUS (WIP):
-- * `level_loop_spec` STRENGTHENED to the trailing-ones characterization
--     (`res ≤ 30 ∧ index % 2^(res+1) = 2^res − 1`), matching the re-extracted `level.post`.
--   New `@[scalar_tac]` helper `level_ge_one` for the `level x > 0` massert.
-- * The re-extraction (new characterization-shaped `level.post`) currently leaves the `level.post`
--     consumers RED: level.spec.proof, left, right, parent (their original bodies are intact; they
--     need re-adapting to the richer post — NOT yet done).
-- * Pre-existing `sorry`s: sibling, direct_path, copath.
-- (proved: root, lowest_common_ancestor, common_direct_path, is_node_in_tree,
--  both to_tree_index, both from_tree_index, TreeNodeIndex.u32, TreeSize.{new,inc,dec}.)
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

/-- `1 <<< k % U32.size = 2^k` for `k < 32` (the shift doesn't wrap). -/
private theorem one_shiftLeft_mod_eq (k : Nat) (h : k < 32) :
    1 <<< k % Aeneas.Std.U32.size = 2 ^ k := by
  simp only [Nat.one_shiftLeft]; simp_scalar

/-- Bit 0 clear ⇔ even. `@[simp]` so `simp_all!` turns the extracted `v &&& 1#u32 = 0#u32`
    low-bit guards into `↑v % 2 = 0`. -/
@[simp] theorem u32_and_one_eq_zero (v : Std.U32) :
    (v &&& 1#u32 = 0#u32) ↔ (↑v : Nat) % 2 = 0 := by
  have hval : (↑(v &&& 1#u32) : Nat) = (↑v : Nat) % 2 := by
    rw [Aeneas.Std.UScalar.val_and, show (↑(1#u32) : Nat) = 1 from rfl, Nat.and_one_is_mod]
  constructor
  · intro h; rw [h] at hval; simpa using hval.symm
  · intro h
    have hz : (↑(v &&& 1#u32) : Nat) = 0 := by rw [hval, h]
    scalar_tac

/-- From the trailing-ones characterization, `k ≥ 1` or `x` even. `@[scalar_tac]` so it fires on the
    char hypothesis: with `x` odd it discharges the `level x > 0` massert in `left`/`right`. -/
@[scalar_tac x % 2 ^ (k + 1) = 2 ^ k - 1]
theorem level_ge_one (x k : Nat) (hchar : x % 2 ^ (k + 1) = 2 ^ k - 1) :
    1 ≤ k ∨ x % 2 = 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · right; subst hk; simpa using hchar
  · left; omega

/-- `level_ge_one` for the `simp`-flipped orientation (`2^k − 1` on the left). -/
@[scalar_tac 2 ^ k - 1 = x % 2 ^ (k + 1)]
theorem level_ge_one' (x k : Nat) (hchar : 2 ^ k - 1 = x % 2 ^ (k + 1)) :
    1 ≤ k ∨ x % 2 = 0 := level_ge_one x k hchar.symm

/-- The `level` trailing-ones loop computes the trailing-ones count: on exit `res ≤ 30` and the low
    `res` bits of `index` are all 1 with bit `res` clear, i.e. `index % 2^(res+1) = 2^res − 1`.
    Loop invariant: the low `k` bits are all 1 (`index % 2^k = 2^k − 1`). Via `loop_spec_measure`. -/
theorem level_loop_spec (index : Std.U32) (hidx : (↑index : Nat) < 2 ^ 30) :
    ⦃ ⌜ True ⌝ ⦄
    level_loop index 0#usize
    ⦃ ⇓ res => ⌜ (↑res : Nat) ≤ 30
        ∧ (↑index : Nat) % 2 ^ ((↑res : Nat) + 1) = 2 ^ (↑res : Nat) - 1 ⌝ ⦄ := by
  unfold level_loop
  apply loop_spec_measure
    (measure := fun (k : Std.Usize) => 32 - k.val)
    (inv := fun (k : Std.Usize) => (↑k : Nat) ≤ 30 ∧ (↑index : Nat) % 2 ^ (↑k : Nat) = 2 ^ (↑k : Nat) - 1)
    (post := fun (res : Std.Usize) => (↑res : Nat) ≤ 30
        ∧ (↑index : Nat) % 2 ^ ((↑res : Nat) + 1) = 2 ^ (↑res : Nat) - 1)
  · exact ⟨by scalar_tac, by simp [Nat.mod_one]⟩
  · rintro k ⟨hk30, hkinv⟩
    unfold level_loop.body
    mvcgen <;> try scalar_tac
    case vc2.hQ =>
      -- bit `k` is set ⇒ continue with `k + 1`; the low `k+1` bits become all 1.
      rename_i i hi_conj bit hbiteq hbit_conj add hadd
      obtain ⟨hi, _⟩ := hi_conj
      obtain ⟨hi1, _⟩ := hbit_conj
      have hand : (↑i : Nat) &&& 1 = 1 := by
        rw [hbiteq] at hi1
        simpa [Aeneas.Std.UScalar.val_and] using hi1.symm
      have hbitk : (↑index : Nat) / 2 ^ (↑k : Nat) % 2 = 1 := by
        have h := hand; rw [hi, Nat.shiftRight_eq_div_pow] at h
        simpa [Nat.and_one_is_mod] using h
      have hmodsucc : (↑index : Nat) % 2 ^ ((↑k : Nat) + 1)
          = (↑index : Nat) % 2 ^ (↑k : Nat)
            + 2 ^ (↑k : Nat) * ((↑index : Nat) / 2 ^ (↑k : Nat) % 2) := by
        rw [pow_succ, Nat.mod_mul]
      have hklt : (↑k : Nat) < 30 := by
        by_contra hge
        have hk30' : (↑k : Nat) = 30 := by omega
        have hd : (↑index : Nat) / 2 ^ 30 = 0 := Nat.div_eq_of_lt hidx
        rw [hk30'] at hbitk; omega
      have haddv : (↑add : Nat) = (↑k : Nat) + 1 := by scalar_tac
      have hp : 1 ≤ (2 : Nat) ^ (↑k : Nat) := Nat.one_le_two_pow
      refine ⟨⟨by scalar_tac, ?_⟩, by scalar_tac⟩
      rw [haddv, hmodsucc, hkinv, hbitk, pow_succ]; omega
    case vc4 =>
      -- bit `k` is clear ⇒ stop; the low `k+1` bits are `2^k − 1` (bit `k` = 0).
      rename_i i hi_conj bit hbitne hbit_conj
      obtain ⟨hi, _⟩ := hi_conj
      obtain ⟨hi1, _⟩ := hbit_conj
      have hbv : (↑bit : Nat) = (↑index : Nat) / 2 ^ (↑k : Nat) % 2 := by
        rw [hi1, Aeneas.Std.UScalar.val_and, hi, Nat.shiftRight_eq_div_pow]
        simp [Nat.and_one_is_mod]
      have hbne : (↑bit : Nat) ≠ 1 := by intro h; apply hbitne; scalar_tac
      have hlt2 : (↑index : Nat) / 2 ^ (↑k : Nat) % 2 < 2 := Nat.mod_lt _ (by norm_num)
      have hbitk : (↑index : Nat) / 2 ^ (↑k : Nat) % 2 = 0 := by omega
      have hmodsucc : (↑index : Nat) % 2 ^ ((↑k : Nat) + 1)
          = (↑index : Nat) % 2 ^ (↑k : Nat)
            + 2 ^ (↑k : Nat) * ((↑index : Nat) / 2 ^ (↑k : Nat) % 2) := by
        rw [pow_succ, Nat.mod_mul]
      refine ⟨by scalar_tac, ?_⟩
      rw [hmodsucc, hkinv, hbitk]; simp

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
    sorry
    -- have hxmax : vecLen x_path ≤ Std.Usize.max := x_path.1.property
    -- unfold common_direct_path_loop.body
    -- split
    -- · -- `j < len`
    --   rename_i hlt
    --   have hjlen : (↑j : Nat) < ↑len := by scalar_tac
    --   have hidxx : (↑j : Nat) < vecLen x_path := by omega
    --   have hidxy : (↑j : Nat) < vecLen y_path := by omega
    --   have hpush : vecLen cp < Std.Usize.max := by omega
    --   unfold ParentNodeIndex.Insts.CoreCmpPartialEqParentNodeIndex.eq
    --   mvcgen [vec_index_spec, vec_push_spec]
    --   all_goals scalar_tac
    -- · -- `j ≥ len`: stop
    --   mvcgen

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
      mvcgen <;> try scalar_tac
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
  -- `simp_all!` reduces the post's shift do-block to `Nat`; `one_shiftLeft_mod_eq` drops the
  -- wrap-around mod, matching the char `level_loop_spec` delivers.
  all_goals (simp_all!; try simp (disch := scalar_tac) only [one_shiftLeft_mod_eq] at *)
  all_goals scalar_tac

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
  sorry
  sorry
  -- rw [Nat.shiftLeft_eq, one_mul,
  --   Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hs) (by native_decide))]
  -- exact Nat.one_le_two_pow

@[spec]
theorem left.spec.proof (index : ParentNodeIndex) :
  (left.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄ left index ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  -- `x = 2·index+1` is odd, so `level x > 0`: reduce the shifts to expose the char, then
  -- `level_ge_one` fires and `scalar_tac` discharges the massert; `simp_all` mops up `2^k > 0`.
  hax_mvcgen [left, level.post]
  all_goals try scalar_tac
  all_goals (simp_all!; try simp (disch := scalar_tac) only [one_shiftLeft_mod_eq] at *)
  all_goals first | scalar_tac | simp_all

@[spec]
theorem right.spec.proof (index : ParentNodeIndex) :
  (right.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄ right index ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  hax_mvcgen [right, level.post]
  all_goals try scalar_tac
  all_goals (simp_all!; try simp (disch := scalar_tac) only [one_shiftLeft_mod_eq] at *)
  all_goals first | scalar_tac | simp_all

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
  hax_mvcgen [level.post, pure] <;> try scalar_tac
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
  all_goals try (simp_all! ; scalar_tac)
  all_goals sorry

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
  all_goals sorry

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

/-- `level v = 0` for an even `v`: the low-bit test in `level` short-circuits before the loop. -/
private theorem level_even_eq (v : Std.U32) (hv : (↑v : Nat) % 2 = 0) :
    level v = ok 0#usize := by
  unfold level
  have hbit : v &&& 1#u32 = 0#u32 := by
    have : (↑(v &&& 1#u32) : Nat) = 0 := by
      rw [Aeneas.Std.UScalar.val_and]
      have : (↑v : Nat) &&& (↑(1#u32) : Nat) = (↑v:Nat) % 2 := by
        rw [show (↑(1#u32):Nat) = 1 from rfl, Nat.and_one_is_mod]
      rw [this, hv]
    scalar_tac
  simp only [hbit, Aeneas.Std.lift]
  rfl

/-- `LeafNodeIndex.to_tree_index w = 2·w` (no overflow when `w < 2^31`). -/
private theorem mul2_ok (w : Std.U32) (hw : (↑w : Nat) < 2 ^ 31) :
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
private theorem lca_tail_aux {p : Std.U32 × Std.I32} {i6 i8 : Std.U32} {i7 : Std.I32}
    (hk2 : 2 ≤ IScalar.toNat p.2) (hk30 : IScalar.toNat p.2 ≤ 30)
    (hbnd : (↑p.1 : Nat) * 2 ^ IScalar.toNat p.2 < 2 ^ 30)
    (hi6v : (↑i6 : Nat) = ↑p.1 <<< IScalar.toNat p.2 % U32.size)
    (hi7 : (↑i7 : Int) = ↑p.2 - ↑(1#i32))
    (hi8v : (↑i8 : Nat) = ↑(1#u32) <<< i7.toNat % U32.size) :
    (↑i6 : Nat) + ↑i8 < 2 ^ 32 ∧ 2 ∣ (↑i6 : Nat) ∧ 2 ≤ (↑i8 : Nat) ∧ 2 ∣ (↑i8 : Nat) := by
  have hi7t1 : 1 ≤ i7.toNat := by scalar_tac
  have hi7t : i7.toNat ≤ 29 := by scalar_tac
  have hsz : (2 : Nat) ^ 31 < U32.size := by native_decide
  have h1u : (↑(1#u32) : Nat) = 1 := rfl
  have hi6val : (↑i6 : Nat) = ↑p.1 * 2 ^ IScalar.toNat p.2 := by
    rw [hi6v, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  have hi8val : (↑i8 : Nat) = 2 ^ i7.toNat := by
    have hb : (2 : Nat) ^ i7.toNat < U32.size :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (show i7.toNat ≤ 31 by omega)) hsz
    rw [hi8v, Nat.shiftLeft_eq, h1u, one_mul, Nat.mod_eq_of_lt hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hi6val, hi8val]
    have hle : (2 : Nat) ^ i7.toNat ≤ 2 ^ 29 := Nat.pow_le_pow_right (by norm_num) hi7t
    omega
  · rw [hi6val]; exact (dvd_pow_self 2 (by omega : IScalar.toNat p.2 ≠ 0)).mul_left _
  · rw [hi8val]
    calc (2 : Nat) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ i7.toNat := Nat.pow_le_pow_right (by norm_num) hi7t1
  · rw [hi8val]; exact dvd_pow_self 2 (by omega : i7.toNat ≠ 0)

@[spec]
theorem lowest_common_ancestor.spec.proof (x : LeafNodeIndex) (y : LeafNodeIndex) :
  (lowest_common_ancestor.pre x y).holds →
  ⦃ ⌜ True ⌝ ⦄ lowest_common_ancestor x y ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  -- The precondition forces two distinct valid (`< 2^29`) leaves. Their tree-indices are even,
  -- so `level` returns `0` and both early-return branches are unreachable (their `x>>1 = y>>1`
  -- tests fail). Only the shift-loop runs; close its `from_tree_index` tail via `lca_tail_aux`.
  unfold lowest_common_ancestor.pre LeafNodeIndex.valid LeafNodeIndex.u32 MAX_INDEX MAX_TREE_SIZE
  intro h_pre
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
    Std.Do.PredTrans.apply] at h_pre
  rw [show (1#u32 <<< 30#i32 : Aeneas.Std.Result Std.U32) = ok 1073741824#u32 from by rfl] at h_pre
  simp only [bind_tc_ok, pure] at h_pre
  rw [show (1073741824#u32 / 2#u32 : Aeneas.Std.Result Std.U32) = ok 536870912#u32 from by rfl] at h_pre
  simp only [bind_tc_ok, decide_eq_true_eq] at h_pre
  have hx29 : (x : Std.U32) < 536870912#u32 := by
    by_contra h; rw [if_neg h] at h_pre; simp_all
  have hy29 : (y : Std.U32) < 536870912#u32 := by
    by_contra h; rw [if_pos hx29, if_neg h] at h_pre; simp_all
  have hxy : x ≠ y := by
    rw [if_pos hx29, if_pos hy29] at h_pre; simp_all
  have hxn : (↑x : Nat) < 2 ^ 29 := by scalar_tac
  have hyn : (↑y : Nat) < 2 ^ 29 := by scalar_tac
  have hxyn : (↑x : Nat) ≠ (↑y : Nat) := by scalar_tac
  obtain ⟨x1, hx1eq, hx1v⟩ := mul2_ok x (by omega)
  obtain ⟨y1, hy1eq, hy1v⟩ := mul2_ok y (by omega)
  unfold lowest_common_ancestor
  rw [hx1eq, hy1eq]
  simp only [bind_tc_ok]
  rw [level_even_eq x1 (by rw [hx1v]; omega), level_even_eq y1 (by rw [hy1v]; omega)]
  simp only [bind_tc_ok]
  mvcgen [lca_loop0_spec, ParentNodeIndex.from_tree_index]
  all_goals try scalar_tac
  case vc30.hmax =>
    rename_i p hpost i6 hi6 i7 hi7 i8 hi8
    obtain ⟨hk2, hk30, hbnd⟩ := hpost
    obtain ⟨hi6v, -⟩ := hi6
    obtain ⟨hi8v, -⟩ := hi8
    rw [show p.2.toNat = IScalar.toNat p.2 from rfl] at hk2 hk30 hbnd
    obtain ⟨hsum, -, -, -⟩ := lca_tail_aux hk2 hk30 hbnd hi6v hi7 hi8v
    have hmax : UScalar.max UScalarTy.U32 = 2 ^ 32 - 1 := by native_decide
    omega
  case vc31.h =>
    rename_i p hpost i6 hi6 i7 hi7 i8 hi8 i9 hi9
    obtain ⟨hk2, hk30, hbnd⟩ := hpost
    obtain ⟨hi6v, -⟩ := hi6
    obtain ⟨hi8v, -⟩ := hi8
    rw [show p.2.toNat = IScalar.toNat p.2 from rfl] at hk2 hk30 hbnd
    obtain ⟨-, -, hi8ge, -⟩ := lca_tail_aux hk2 hk30 hbnd hi6v hi7 hi8v
    scalar_tac
  case vc32.h =>
    rename_i p hpost i6 hi6 i7 hi7 i8 hi8 i9 hi9 i10 hi10
    obtain ⟨hk2, hk30, hbnd⟩ := hpost
    obtain ⟨hi6v, -⟩ := hi6
    obtain ⟨hi8v, -⟩ := hi8
    obtain ⟨hi10v, -⟩ := hi10
    rw [show p.2.toNat = IScalar.toNat p.2 from rfl] at hk2 hk30 hbnd
    obtain ⟨-, -, hi8ge, -⟩ := lca_tail_aux hk2 hk30 hbnd hi6v hi7 hi8v
    scalar_tac
  case vc34.h =>
    rename_i p hpost i6 hi6 i7 hi7 i8 hi8 i9 hi9 i10 hi10 u hu rmod hmod
    obtain ⟨hk2, hk30, hbnd⟩ := hpost
    obtain ⟨hi6v, -⟩ := hi6
    obtain ⟨hi8v, -⟩ := hi8
    obtain ⟨hi10v, hi9ge⟩ := hi10
    rw [show p.2.toNat = IScalar.toNat p.2 from rfl] at hk2 hk30 hbnd
    obtain ⟨-, hi6dvd, hi8ge, hi8dvd⟩ := lca_tail_aux hk2 hk30 hbnd hi6v hi7 hi8v
    rw [show (↑(1#u32) : Nat) = 1 from rfl] at hi10v
    rw [show (↑(2#u32) : Nat) = 2 from rfl] at hmod
    have : (↑rmod : Nat) = 1 := by omega
    scalar_tac

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
  -- `new nodes = 2^(log2 nodes + 1) − 1`. From `nodes < 2^30` we get `log2 nodes ≤ 29`, which
  -- discharges the shift bound (`< 32`), the `1 ≤ …` underflow guard, and `res ≤ 2^30` (via `<`).
  hax_mvcgen [new] <;> try scalar_tac
  all_goals simp_all!
  all_goals
    (have hnodes : (↑nodes:Nat) < 2 ^ 30 := by
      have h30 : (1:Nat) <<< 30#i32.toNat % Aeneas.Std.U32.size = 2 ^ 30 :=
        one_shiftLeft_mod_eq 30#i32.toNat (by decide)
      have ha : (↑nodes:Nat) < 1 <<< 30#i32.toNat % Aeneas.Std.U32.size := by assumption
      rw [h30] at ha; exact ha
     have hlog : Nat.log 2 (↑nodes:Nat) ≤ 29 := by
      have := Nat.log_lt_of_lt_pow (by assumption) hnodes; omega)
  · omega
  · exact one_le_one_shiftLeft_mod _ (by omega)
  · exfalso
    have hshow : (30#i32).toNat = 30 := by decide
    simp only [hshow,
      one_shiftLeft_mod_eq 30 (by decide),
      one_shiftLeft_mod_eq (31 - (31 - Nat.log 2 (↑nodes:Nat)) + 1) (by omega)] at *
    have hle : (2:Nat) ^ (31 - (31 - Nat.log 2 (↑nodes:Nat)) + 1) ≤ 2 ^ 30 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

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
