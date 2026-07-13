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
  MAX_TREE_SIZE MIN_TREE_SIZE MAX_INDEX
  --
  log2
  is_node_in_tree
  --
  TreeSize.u32
  TreeSize.leaf_count
  --
  TreeNodeIndex.new
  TreeNodeIndex.u32
  --
  LeafNodeIndex.new
  LeafNodeIndex.u32
  LeafNodeIndex.to_tree_index
  LeafNodeIndex.from_tree_index
  --
  ParentNodeIndex.new
  ParentNodeIndex.u32
  ParentNodeIndex.to_tree_index
  ParentNodeIndex.from_tree_index


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
theorem level.spec.proof : ∀ (index : Std.U32),
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

/-- `TreeNodeIndex.new` never panics, and the node it builds round-trips back to `index`
    under `.u32`: the `is_multiple_of` test it branches on is exactly the parity that the
    chosen `from_tree_index` then asserts. -/
@[spec]
theorem TreeNodeIndex.new_spec
    (index : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄
    new index
    ⦃ ⇓ tni => ⌜ ⦃ ⌜ True ⌝ ⦄ u32 tni ⦃ ⇓ r => ⌜ r = index ⌝ ⦄ ⌝ ⦄ := by
  hax_mvcgen [ core.num.U32.is_multiple_of ]
  all_goals try scalar_tac

@[spec]
theorem root.spec.proof
  (size : TreeSize) :
  (root.pre size).holds →
  ⦃ ⌜ True ⌝ ⦄
  root size
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  unfold root.pre
  intro h_pre
  hax_mvcgen [root]
  <;> (try scalar_tac)
  <;> (try grind)
  · rename_i hr1 hr1eq hr hreq
    obtain ⟨hreq, _⟩ := hreq
    obtain ⟨hr1eq, hlz⟩ := hr1eq
    have hlt : (↑(UScalar.cast UScalarTy.Usize hr1) : Nat) < 32 := by scalar_tac
    have hpos := one_le_one_shiftLeft_mod _ hlt
    rw [hreq]; scalar_tac

@[spec]
theorem left.spec.proof
  (index : ParentNodeIndex) : left.spec index := by
  unfold spec pre
  intro h_pre
  hax_mvcgen [left, level.post]
  <;> scalar_tac

@[spec]
theorem right.spec.proof
  (index : ParentNodeIndex) :
  (right.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄
  right index
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  unfold right.pre
  intro h_pre
  hax_mvcgen [right, level.post]
  <;> scalar_tac

/-- Value characterization of `level`: the result `n` is the number of trailing 1-bits,
    i.e. the low `n` bits of `index` are all 1 and bit `n` is 0 (`index % 2^(n+1) = 2^n - 1`). -/
theorem level_char (index : Std.U32) (hx : (↑index : Nat) < 2 ^ 31) :
    ⦃ ⌜ True ⌝ ⦄
    level index
    ⦃ ⇓ n => ⌜ (↑n : Nat) ≤ 31 ∧ (↑index : Nat) % 2 ^ ((↑n : Nat) + 1) = 2 ^ (↑n : Nat) - 1 ⌝ ⦄ := by
  unfold level
  hax_mvcgen [level_loop]
  case vc1 =>
    -- `index` even: level is 0, and `index % 2 = 0`.
    rename_i hr0 hr
    refine ⟨by scalar_tac, ?_⟩
    have hv : (↑(index &&& 1#u32) : Nat) = (↑index : Nat) &&& 1 := by
      simp [Aeneas.Std.UScalar.val_and]
    have hm := Nat.and_one_is_mod (↑index : Nat)
    have hand : (↑index : Nat) % 2 = 0 := by scalar_tac
    have h0 : (↑(0#usize) : Nat) = 0 := by scalar_tac
    rw [h0]; simpa using hand
  case vc2.success.isFalse =>
    have hspec :
        Aeneas.Std.WP.spec
          (Aeneas.Std.loop
            (fun k1 => level_loop.body index k1)
            0#usize)
          (fun n => (↑n : Nat) ≤ 31 ∧ (↑index : Nat) % 2 ^ ((↑n : Nat) + 1) = 2 ^ (↑n : Nat) - 1) := by
      apply Aeneas.Std.loop.spec_decr_nat
        (measure := fun k => 32 - k.val)
        (inv := fun k => k.val ≤ 31 ∧ (↑index : Nat) % 2 ^ (k.val) = 2 ^ (k.val) - 1)
      · intro k hk
        obtain ⟨hk31, hkinv⟩ := hk
        unfold level_loop.body
        step as ⟨i, hi⟩
        step as ⟨i1, hi1⟩
        -- `i1 = (index >>> k) & 1` is bit `k` of `index`
        have hbitk : (↑i1 : Nat) = (↑index : Nat) / 2 ^ (k.val) % 2 := by
          rw [hi1, Aeneas.Std.UScalar.val_and, hi, Nat.shiftRight_eq_div_pow]
          simp [Nat.and_one_is_mod]
        have hmodsucc : (↑index : Nat) % 2 ^ (k.val + 1)
            = (↑index : Nat) % 2 ^ (k.val) + 2 ^ (k.val) * ((↑index : Nat) / 2 ^ (k.val) % 2) := by
          rw [pow_succ, Nat.mod_mul]
        have hp : 1 ≤ 2 ^ (k.val) := Nat.one_le_two_pow
        split
        · -- bit `k` set: continue with `k + 1`
          rename_i hc
          step as ⟨k1, hk1⟩
          have hbit1 : (↑index : Nat) / 2 ^ (k.val) % 2 = 1 := by
            rw [← hbitk]; scalar_tac
          have hklt : k.val < 31 := by
            by_contra hge
            have hk31' : k.val = 31 := by omega
            have hd : (↑index : Nat) / 2 ^ 31 = 0 := Nat.div_eq_of_lt hx
            rw [hk31'] at hbit1; omega
          refine ⟨?_, ?_, ?_⟩
          · rw [hk1]; omega
          · rw [hk1, hmodsucc, hkinv, hbit1, pow_succ]; omega
          · rw [hk1]; omega
        · -- bit `k` clear: stop, returning `k`
          rename_i hc
          simp only [Aeneas.Std.WP.spec_ok]
          refine ⟨hk31, ?_⟩
          have hbit0 : (↑index : Nat) / 2 ^ (k.val) % 2 = 0 := by
            have hne : (↑i1 : Nat) ≠ 1 := by intro h; apply hc; scalar_tac
            rw [hbitk] at hne; omega
          rw [hmodsucc, hkinv, hbit0]; simp
      · exact ⟨by scalar_tac, by simp [Nat.mod_one]⟩
    -- the loop spec's postcondition matches the goal exactly
    mspec (Aeneas.Std.WP.spec_to_mvcgen hspec)

-- `direct_path.spec.proof`, `copath.spec.proof`, and `lowest_common_ancestor.spec.proof`
-- are proved at the end of this file (they need `loop_spec_measure` and the `parent`/`root`
-- value specs, all defined below).

open binary_tree.array_representation.treemath in
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

-- `common_direct_path.spec.proof` is proved at the end of this file (it calls `direct_path`,
-- so it must come after `direct_path.spec.proof`).

theorem is_node_in_tree.spec.proof
   (node_index : TreeNodeIndex)
  (size : TreeSize) :
  (is_node_in_tree.pre node_index
  size).holds →
  ⦃ ⌜ True ⌝ ⦄
  is_node_in_tree node_index size
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  intro h_pre
  cases node_index <;>
  hax_mvcgen
  all_goals scalar_tac

/-! ## `lowest_common_ancestor` panic-freedom

   Leaf tree-indices are even, so `level` of both is `0` and `lx = ly = 1`. The two early
   returns are never taken (each would `from_tree_index` an even value), so only `loop0`
   runs. Its result `(xn << k) + (1 << (k-1)) - 1` is odd because the loop runs at least
   twice (`k ≥ 2`) on two distinct even inputs below `2^30`. -/

/-- `level` of an even `u32` (below `2^31`) is `0`: bit 0 is clear. -/
theorem level_even (x : Std.U32) (hx : (↑x : Nat) < 2 ^ 31) (he : (↑x : Nat) % 2 = 0) :
    ⦃ ⌜ True ⌝ ⦄
    level x
    ⦃ ⇓ r => ⌜ (↑r : Nat) = 0 ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_wp
  apply Std.Do.Triple.entails_wp_of_post (level_char x hx)
  simp only [PostCond.entails]
  refine ⟨fun r => ?_, by simp⟩
  intro hr
  obtain ⟨hr31, hmod⟩ := hr
  by_contra hne
  have hd : (2 : Nat) ∣ 2 ^ ((↑r : Nat) + 1) := dvd_pow_self 2 (Nat.succ_ne_zero _)
  have h1 := Nat.mod_mod_of_dvd (↑x : Nat) hd
  rw [hmod] at h1
  have he2 : (2 : Nat) ^ (↑r : Nat) % 2 = 0 := by
    have hdr : (2 : Nat) ∣ 2 ^ (↑r : Nat) := dvd_pow_self 2 hne
    omega
  have hge : 2 ≤ (2 : Nat) ^ (↑r : Nat) := by
    calc (2 : Nat) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (↑r : Nat) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `level` of an even `u32` below `2^31` evaluates to exactly `ok 0`. Phrased as an
    equation so it can rewrite the `level` call away (the generic `level` spec's
    `level.post` postcondition does not reduce under `mvcgen`). -/
theorem level_even_eq (x : Std.U32) (hx : (↑x : Nat) < 2 ^ 31) (he : (↑x : Nat) % 2 = 0) :
    level x = ok 0#usize := by
  obtain ⟨r, hr⟩ := triple_noThrow_exists_ok (level_even x hx he)
  have hpost := triple_noThrow_elim (level_even x hx he) hr
  simp only [SPred.down_pure] at hpost
  have hr0 : r = 0#usize := by scalar_tac
  rw [hr, hr0]

/-- Doubling a `u32` below `2^31` never overflows; the result is `2·z`. Phrased as an
    explicit `ok`-equation so the `to_tree_index` multiplication can be rewritten away,
    exposing the leaf tree-index as a concrete value. -/
theorem mul2_ok (z : Std.U32) (h : (↑z : Nat) < 2 ^ 31) :
    ∃ w : Std.U32, z * 2#u32 = ok w ∧ (↑w : Nat) = 2 * ↑z := by
  have he := Aeneas.Std.UScalar.mul_equiv z 2#u32
  have hmul : (z * 2#u32 : Aeneas.Std.Result Std.U32) = Aeneas.Std.UScalar.mul z 2#u32 := rfl
  rw [hmul]
  cases hm : Aeneas.Std.UScalar.mul z 2#u32 with
  | ok w =>
    rw [hm] at he
    obtain ⟨_, hval, _⟩ := he
    exact ⟨w, rfl, by rw [hval]; scalar_tac⟩
  | fail e => rw [hm] at he; simp only at he; scalar_tac
  | div => rw [hm] at he; exact absurd he (by simp)

/-- Shared arithmetic for the `from_tree_index ((xn << k) + (1 << (k-1)) - 1)` tail of
    `lowest_common_ancestor`, given `loop0`'s postcondition (`2 ≤ k ≤ 30`, `xn·2^k < 2^30`):
    the two shifts don't wrap, their sum stays below `2^32`, `xn<<k` is even, and `1<<(k-1)`
    is an even value `≥ 2` (so the final `−1` is odd and positive). -/
theorem lca_tail_aux {p : Std.U32 × Std.I32} {i6 i8 : Std.U32} {i7 : Std.I32}
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

open binary_tree.array_representation.treemath in
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

@[spec]
theorem lowest_common_ancestor.spec.proof
   (x : LeafNodeIndex)
  (y : LeafNodeIndex) :
  (lowest_common_ancestor.pre x
  y).holds →
  ⦃ ⌜ True ⌝ ⦄
  lowest_common_ancestor x y
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  unfold lowest_common_ancestor.pre
  intro h_pre
  hax_mvcgen [lowest_common_ancestor, pure, level.post]
  sorry
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

open binary_tree.array_representation.treemath in
/-- `new x` then `.u32` round-trips to `x` as explicit `ok`-equations: the parity test in
    `new` chooses the `from_tree_index` whose `to_tree_index` inverts it. -/
theorem new_u32_eq (x : Std.U32) :
    ∃ tni, TreeNodeIndex.new x = ok tni ∧ TreeNodeIndex.u32 tni = ok x := by
  obtain ⟨tni, htni⟩ := triple_noThrow_exists_ok (TreeNodeIndex.new_spec x)
  have hpost := triple_noThrow_elim (TreeNodeIndex.new_spec x) htni
  simp only [SPred.down_pure] at hpost
  obtain ⟨r, hr⟩ := triple_noThrow_exists_ok hpost
  have hrx := triple_noThrow_elim hpost hr
  simp only [SPred.down_pure] at hrx
  exact ⟨tni, htni, by rw [hr, hrx]⟩

/-- `level x` evaluates to exactly the trailing-ones count `tones ↑x` (≤ 31), as an
    explicit `ok`-equation so the `level` call can be rewritten away before `mvcgen`. -/
theorem level_tones_eq (x : Std.U32) (hx : (↑x : Nat) < 2 ^ 31) :
    ∃ k : Std.Usize, level x = ok k
      ∧ (↑k : Nat) = tones ↑x ∧ (↑k : Nat) ≤ 31 := by
  obtain ⟨k, hk⟩ := triple_noThrow_exists_ok (level_char x hx)
  have hpost := triple_noThrow_elim (level_char x hx) hk
  simp only [SPred.down_pure] at hpost
  obtain ⟨hk31, hmod⟩ := hpost
  exact ⟨k, hk, trailing_unique ↑x (↑k) (tones ↑x) hmod (tones_mod ↑x), hk31⟩

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

open binary_tree.array_representation.treemath in
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

open binary_tree.array_representation.treemath in
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

/-- `log2 s = Nat.log 2 s` for nonzero `s` (`leading_zeros` semantics). -/
theorem log2_eq (s : Std.U32) (hpos : 0 < (↑s : Nat)) :
    ∃ dd : Std.Usize, log2 s = ok dd
      ∧ (↑dd : Nat) = Nat.log 2 (↑s : Nat) := by
  have hs0 : s ≠ 0#u32 := by intro h; rw [h] at hpos; simp at hpos
  have hs32 : (↑s : Nat) < 2 ^ 32 := by scalar_tac
  have hL31 : Nat.log 2 (↑s : Nat) ≤ 31 := by
    by_contra hc
    have hge : (2 : Nat) ^ 32 ≤ (↑s : Nat) :=
      calc (2 : Nat) ^ 32 ≤ 2 ^ (Nat.log 2 (↑s : Nat)) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ (↑s : Nat) := Nat.pow_log_le_self 2 (by omega)
    omega
  -- value of `leading_zeros s`
  have hbv : s.bv ≠ 0 := by
    intro h
    have : (↑s : Nat) = 0 := by rw [show (↑s : Nat) = s.bv.toNat from rfl, h]; simp
    omega
  have hlz : (↑(Aeneas.Std.core.num.U32.leading_zeros s) : Nat) = 31 - Nat.log 2 (↑s : Nat) := by
    unfold Aeneas.Std.core.num.U32.leading_zeros Aeneas.Std.BitVec.leadingZeros
    rw [if_neg hbv]
    show (BitVec.ofNat 32 (32 - Nat.log 2 s.bv.toNat - 1)).toNat = 31 - Nat.log 2 (↑s : Nat)
    rw [BitVec.toNat_ofNat, show s.bv.toNat = (↑s : Nat) from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  unfold log2
  rw [if_neg hs0]
  rw [show core.num.U32.leading_zeros s = ok (Aeneas.Std.core.num.U32.leading_zeros s) from rfl]
  simp only [bind_tc_ok]
  set lz := Aeneas.Std.core.num.U32.leading_zeros s with hlzdef
  have hle : (↑lz : Nat) ≤ 31 := by rw [hlz]; omega
  have h31 : (↑(31#u32) : Nat) = 31 := by rfl
  have hsub := Aeneas.Std.UScalar.sub_equiv 31#u32 lz
  cases hc : (31#u32 - lz) with
  | ok i1 =>
    rw [hc] at hsub
    obtain ⟨_, hval, _⟩ := hsub
    simp only [hc, bind_tc_ok]
    refine ⟨_, rfl, ?_⟩
    have hi1 : (↑i1 : Nat) = Nat.log 2 (↑s : Nat) := by omega
    scalar_tac
  | fail e => rw [hc] at hsub; simp only at hsub; omega
  | div => rw [hc] at hsub; exact absurd hsub (by simp)

/-- `log2` as a `Triple`, for `mvcgen`. -/
theorem log2_spec (s : Std.U32) (hpos : 0 < (↑s : Nat)) :
    ⦃ ⌜ True ⌝ ⦄ log2 s
    ⦃ ⇓ dd => ⌜ (↑dd : Nat) = Nat.log 2 (↑s : Nat) ⌝ ⦄ := by
  obtain ⟨dd, hlog, hdd⟩ := log2_eq s hpos
  exact triple_of_ok hlog hdd

open binary_tree.array_representation.treemath in
/-- `new x` then `.u32` round-trips, as a `Triple`. -/
theorem new_u32_triple (x : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄ (do let tni ← TreeNodeIndex.new x; TreeNodeIndex.u32 tni)
    ⦃ ⇓ r => ⌜ r = x ⌝ ⦄ := by
  obtain ⟨tni, h1, h2⟩ := new_u32_eq x
  rw [h1]; simp only [bind_tc_ok]; exact triple_of_ok h2 rfl

open binary_tree.array_representation.treemath in
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

open binary_tree.array_representation.treemath in
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
  · exact ⟨ht0, hx0, hvec0, helem0⟩
  · intro p hinv
    obtain ⟨vec, xv⟩ := p
    obtain ⟨htones, hxlt, hvlen, helem⟩ := hinv
    simp only at htones hxlt hvlen helem ⊢
    unfold direct_path_loop.body
    split
    · rename_i hcond
      have hxvr : (↑xv : Nat) ≠ (↑r : Nat) := by
        have hne : xv ≠ r := by simpa [bne_iff_ne] using hcond
        scalar_tac
      have htlt : tones (↑xv : Nat) < d := by
        rcases Nat.lt_or_ge (tones (↑xv : Nat)) d with h | h
        · exact h
        · exfalso
          have hmod := tones_mod (↑xv : Nat)
          rw [show tones (↑xv : Nat) = d from by omega] at hmod
          rw [Nat.mod_eq_of_lt hxlt] at hmod
          exact hxvr (by rw [hmod, hr])
      have hxv31 : (↑xv : Nat) < 2 ^ 31 - 1 := small_of_tones _ d hd30 hxlt htones
      have hps := parent_new_spec xv hxv31
      obtain ⟨par, hpar⟩ := triple_noThrow_exists_ok hps
      have hparpost := triple_noThrow_elim hps hpar
      simp only [SPred.down_pure] at hparpost
      rw [← bind_assoc, hpar]
      simp only [bind_tc_ok]
      obtain ⟨hval, hpar31⟩ := hparpost
      -- the pushed element `par` satisfies the bound: `2·par+1 = x1 < 2^31-1`
      have hpar_small : 2 * (↑par : Nat) + 1 < 2 ^ 31 - 1 := by
        have hx1lt : 2 * (↑par : Nat) + 1 < 2 ^ (d + 1) := by
          rw [hval]
          refine parent_lt d (tones ↑xv) (↑xv / 2 ^ (tones ↑xv + 2)) htlt ?_
          refine Nat.div_lt_of_lt_mul ?_
          rw [← pow_add, show (tones ↑xv + 2) + (d - 1 - tones ↑xv) = d + 1 from by omega]
          exact hxlt
        have hx1t : tones (2 * (↑par : Nat) + 1) ≤ d := by rw [hval, tones_parent]; omega
        exact small_of_tones _ d hd30 hx1lt hx1t
      mvcgen [vec_push_spec, ParentNodeIndex.to_tree_index]
      · -- vc1: push precondition `vecLen vec < Usize.max`
        have h30 : vecLen vec ≤ 30 := by omega
        scalar_tac
      · -- vc2: `par * 2 ≤ U32.max`
        have hmax : Aeneas.Std.U32.max = 2 ^ 32 - 1 := by native_decide
        scalar_tac
      · -- vc3: continue — invariant preserved and measure decreases
        rename_i vec' hvpush rmul hmul rfin hfin
        obtain ⟨hvlen', hvval'⟩ := hvpush
        have hx1 : (↑rfin : Nat)
            = 2 ^ (tones ↑xv + 2) * (↑xv / 2 ^ (tones ↑xv + 2)) + (2 ^ (tones ↑xv + 1) - 1) := by
          rw [show (↑(2#u32) : Nat) = 2 from rfl] at hmul
          rw [show (↑(1#u32) : Nat) = 1 from rfl] at hfin
          omega
        have htones1 : tones (↑rfin : Nat) = tones (↑xv : Nat) + 1 := by
          rw [hx1]; exact tones_parent _ _
        have hlt1 : (↑rfin : Nat) < 2 ^ (d + 1) := by
          rw [hx1]
          refine parent_lt d (tones ↑xv) (↑xv / 2 ^ (tones ↑xv + 2)) htlt ?_
          refine Nat.div_lt_of_lt_mul ?_
          rw [← pow_add, show (tones ↑xv + 2) + (d - 1 - tones ↑xv) = d + 1 from by omega]
          exact hxlt
        refine ⟨⟨?_, hlt1, ?_, ?_⟩, ?_⟩
        · rw [htones1]; omega
        · rw [htones1]; omega
        · -- element bound for the grown vec `vec.1.val ++ [par]`
          intro e he
          rw [hvval', List.mem_append] at he
          rcases he with he | he
          · exact helem e he
          · simp only [List.mem_singleton] at he; subst he; exact hpar_small
        · rw [htones1]; omega
      · -- vc4: `par * 2 + 1 ≤ U32.max`
        intro hh
        have hmax : Aeneas.Std.U32.max = 2 ^ 32 - 1 := by native_decide
        scalar_tac
    · mvcgen
      exact ⟨helem, by omega⟩

open binary_tree.array_representation.treemath in
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

open binary_tree.array_representation.treemath in
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

@[spec]
theorem common_direct_path.spec.proof
   (x : LeafNodeIndex)
  (y : LeafNodeIndex)
  (size : TreeSize) :
  (common_direct_path.pre x y
  size).holds →
  ⦃ ⌜ True ⌝ ⦄
  common_direct_path x y size
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  unfold common_direct_path.pre
  intro h_pre
  hax_mvcgen [common_direct_path,
    TreeSize.u32,
    TreeSize.leaf_count,
    LeafNodeIndex.u32,
    MAX_TREE_SIZE]
  all_goals try scalar_tac
  -- vc19: the Vec-machinery tail (deref_mut/reverse/len/min/with_capacity/loop/…), threaded
  -- through the registered `@[spec]` lemmas; each destructuring `deref_mut` bind is reduced by
  -- `mvcgen` stepping then re-threading.
  mvcgen [deref_mut_slice_spec]
  all_goals (first | (intro _; omega) | omega | scalar_tac | mvcgen)

/-! ## `sibling` panic-freedom (for `copath`) -/

open binary_tree.array_representation.treemath in
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

open binary_tree.array_representation.treemath in
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

open binary_tree.array_representation.treemath in
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

open binary_tree.array_representation.treemath in
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

open binary_tree.array_representation.treemath in
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

open binary_tree.array_representation.treemath in
/-- A leaf node `Leaf l` with `2·l < 2^31 − 1` is `sibling`-safe. -/
theorem siblingSafe_leaf (l : LeafNodeIndex)
    (hl : 2 * (↑l : Nat) < 2 ^ 31 - 1) :
    SiblingSafe (TreeNodeIndex.Leaf l) := by
  obtain ⟨w, hw, hwv⟩ := mul2_ok l (by omega : (↑l : Nat) < 2 ^ 31)
  have hu : TreeNodeIndex.u32 (TreeNodeIndex.Leaf l) = ok w := by
    unfold TreeNodeIndex.u32 LeafNodeIndex.to_tree_index; exact hw
  exact sibling_noPanic (TreeNodeIndex.Leaf l) w hu (by rw [hwv]; omega)

open binary_tree.array_representation.treemath in
/-- A parent node `Parent p` with `2·p+1 < 2^31 − 1` is `sibling`-safe. -/
theorem siblingSafe_parent (p : ParentNodeIndex)
    (hp : 2 * (↑p : Nat) + 1 < 2 ^ 31 - 1) :
    SiblingSafe (TreeNodeIndex.Parent p) := by
  obtain ⟨x, htti, hxv⟩ := ptti_ok p (by
    have : (2 : Nat) ^ 31 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
  have hu : TreeNodeIndex.u32 (TreeNodeIndex.Parent p) = ok x := by
    unfold TreeNodeIndex.u32; exact htti
  exact sibling_noPanic (TreeNodeIndex.Parent p) x hu (by rw [hxv]; exact hp)

open binary_tree.array_representation.treemath in
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
