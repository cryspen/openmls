-- [openmls]: treemath panic-freedom — the per-function value specs
import Aeneas
import CoreModels
import Openmls.Extraction.Types
import Openmls.Extraction.Funs
import Openmls.Extraction.Specs
import Openmls.Proofs.Common
import Openmls.Proofs.BitMath
import Openmls.Proofs.PartialSpecs
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
  MAX_TREE_SIZE MIN_TREE_SIZE
  MAX_TREE_INDEX MAX_LEAF MAX_PARENT MAX_LEAF_COUNT MAX_ROOT_INDEX
  --
  --log2
  is_node_in_tree
  --
  TreeSize.u32
  TreeSize.leaf_count
  TreeSize.parent_count
  -- TreeSize.valid
  --
  TreeNodeIndex.new
  TreeNodeIndex.u32
  -- TreeNodeIndex.valid
  --
  LeafNodeIndex.new
  LeafNodeIndex.u32
  LeafNodeIndex.to_tree_index
  LeafNodeIndex.from_tree_index
  -- LeafNodeIndex.valid
  --
  ParentNodeIndex.new
  ParentNodeIndex.u32
  ParentNodeIndex.to_tree_index
  ParentNodeIndex.from_tree_index
  -- ParentNodeIndex.valid


-- ------------------------------------------------------------------------------

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
    case vc1.hQ =>
      -- bit `k` is set ⇒ continue with `k + 1`; the low `k+1` bits become all 1.
      rename_i i hi bit hbiteq hbit_conj add hadd
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
    case vc3 =>
      -- bit `k` is clear ⇒ stop; the low `k+1` bits are `2^k − 1` (bit `k` = 0).
      rename_i i hi bit hbitne hbit_conj
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
    have hxmax : vecLen x_path ≤ Std.Usize.max := x_path.property
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
      mvcgen <;> try scalar_tac
      · rename_i xn1 hxn1 yn1 hyn1 k1 hk1
        have h1 : (1#i32).toNat = 1 := by decide
        have hItn : I32.toNat k1 = k.toNat + 1 := by scalar_tac
        refine ⟨⟨by scalar_tac, by scalar_tac, ?_, ?_⟩, by scalar_tac⟩
        · rw [hxn1, h1, Nat.shiftRight_eq_div_pow, pow_one, hxn, hItn,
              Nat.div_div_eq_div_mul, ← pow_succ]
        · rw [hyn1, h1, Nat.shiftRight_eq_div_pow, pow_one, hyn, hItn,
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

/-- Pure-`Prop` spec for `level`: the trailing-ones characterization, with a pure hypothesis
    pre. User-validated exception to the "generated specs only" rule — `level` occurs inside
    the postconditions of `parent`/`left`/`right`, and re-stepping the monadic `level.post`
    do-block at every use site is a performance blocker. Registered `@[spec]` (in place of
    `level.spec.proof`, which is unregistered): callers step `level` through THIS. -/
@[spec]
theorem level.spec_pure (index : Std.U32) (hidx : (↑index : Nat) < 2 ^ 30) :
    ⦃ ⌜ True ⌝ ⦄
    level index
    ⦃ ⇓ r => ⌜ (↑r : Nat) ≤ 30
        ∧ (↑index : Nat) % 2 ^ ((↑r : Nat) + 1) = 2 ^ (↑r : Nat) - 1 ⌝ ⦄ := by
  -- Even `index`: `level` short-circuits to `0`, and `index % 2 = 0 = 2^0 − 1` (`u32_and_one_eq_zero`).
  -- Odd `index`: the loop runs and `level_loop_spec` is exactly the postcondition.
  unfold level
  mvcgen [level_loop_spec] <;> first | scalar_tac | simp_all

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
  all_goals try scalar_tac


@[spec]
theorem root.spec.proof (size : TreeSize) :
  (root.pre size).holds →
  ⦃ ⌜ True ⌝ ⦄ root size ⦃ ⇓ res => ⌜ (root.post size res).holds ⌝ ⦄
  := by
  -- `root size = TreeNodeIndex.new ((1 <<< log2 size) − 1)`, with the REAL post
  -- `res.valid ∧ res.u32 < size`.
  --
  -- Two things make this work.  First, `root.post` must be unfolded alongside `root.pre` (the
  -- `parent`/`sibling` shape): left folded, `mvcgen` cannot step the post's own inner calls
  -- (`TreeNodeIndex.valid`, `TreeNodeIndex.u32`, `TreeSize.u32`) and the obligations survive as
  -- opaque `.holds` goals.  Unfolded, all 14 VCs come out as plain arithmetic over the registered
  -- specs for `log2` and `TreeNodeIndex.new`.
  --
  -- Second, `TreeSize.valid` arrives as the SELF-REFERENTIAL characterization
  -- `decide (1 ≤ s ∧ s ≤ 2^30 ∧ s = 2^(Nat.log 2 s + 1) − 1) = true`, on which `scalar_tac`'s
  -- preprocessing diverges with an uncatchable `maxRecDepth` abort (reproducer:
  -- `Openmls/Issues/ScalarTacNatLogLoop.lean`).  The documented cure is to make `Nat.log 2 s`
  -- opaque, so the preamble destructures the `decide` term-level with `of_decide_eq_true` FIRST,
  -- then `set`s `L := Nat.log 2 size` and `clear_value`s it — after which no `Nat.log` occurs
  -- anywhere and `scalar_tac` is safe.
  --
  -- The remaining maths is linear in the two atoms `size` and `2^L`, given: `L ≤ 29` (from
  -- `s = 2^(L+1) − 1 ≤ 2^30`, so `2^(L+1) ≤ 2^30 + 1`), `2^(L+1) = 2·2^L`, and the non-wrapping
  -- shift `1 <<< L % U32.size = 2^L`.  Validity then holds because `2^L − 1 ≤ 2^30 − 2`, and the
  -- bound because `2^L − 1 < 2^(L+1) − 1 = size` — in both the `Leaf` (even) and `Parent` (odd)
  -- branches of `TreeNodeIndex.new`, since `2·(x/2) ≤ x` and `2·((x−1)/2) + 1 ≤ x`.
  unfold root.pre root.post
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [root]
  all_goals
    (obtain ⟨hs1, hs2, hs3⟩ :=
        of_decide_eq_true
          (show decide (1 ≤ (↑size : Nat) ∧ (↑size : Nat) ≤ 2 ^ 30 ∧
              (↑size : Nat) = 2 ^ (Nat.log 2 (↑size : Nat) + 1) - 1) = true by assumption)
     set L := Nat.log 2 (↑size : Nat) with hLdef
     clear hLdef
     clear_value L
     have hL29 : L ≤ 29 := by
       by_contra hc
       have : (2 : Nat) ^ 31 ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
       omega
     have hp1 : (1 : Nat) ≤ 2 ^ L := Nat.one_le_two_pow
     have hp29 : (2 : Nat) ^ L ≤ 2 ^ 29 := Nat.pow_le_pow_right (by omega) hL29
     have hpow : (2 : Nat) ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
     have hsh : 1 <<< L % Aeneas.Std.U32.size = 2 ^ L := one_shiftLeft_mod_eq L (by omega)
     try scalar_tac)

@[spec]
theorem left.spec.proof (index : ParentNodeIndex) :
  (left.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄ left index ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  -- `x = 2·index+1` is odd, so `level x > 0`: reduce the shifts to expose the char, then
  -- `level_ge_one` fires and `scalar_tac` discharges the massert; `simp_all` mops up `2^k > 0`.
  hax_mvcgen [left] <;> scalar_tac

@[spec]
theorem right.spec.proof (index : ParentNodeIndex) :
  (right.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄ right index ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  hax_mvcgen [right] <;> scalar_tac

/-- `BitMath.parent_val_u32` in exactly the shape `parent`'s VCs present it: the extracted code
    binds each shift/mask to its own `r`-variable with a `.val` equation, so the value equation has
    to be re-assembled from those equations before the pure lemma applies. -/
private theorem parent_bits_val
    (v r1 r2 rr : U32) (k k1 : Usize)
    (hk30 : (↑k : Nat) ≤ 30)
    (hchar : (↑v : Nat) % 2 ^ ((↑k : Nat) + 1) = 2 ^ (↑k : Nat) - 1)
    (hk1 : (↑k1 : Nat) = (↑k : Nat) + (↑(1#usize) : Nat))
    (hr2 : (↑r2 : Nat) = (↑v : Nat) >>> (↑k1 : Nat))
    (hr1 : (↑r1 : Nat) = (↑(1#u32) : Nat) <<< (↑k : Nat) % UScalar.size UScalarTy.U32)
    (hrr : (↑rr : Nat)
      = (↑(r2 &&& 1#u32) : Nat) <<< (↑k1 : Nat) % UScalar.size UScalarTy.U32) :
    (↑((v ||| r1) ^^^ rr) : Nat)
      = 2 ^ ((↑k : Nat) + 2) * ((↑v : Nat) / 2 ^ ((↑k : Nat) + 2))
        + (2 ^ ((↑k : Nat) + 1) - 1) := by
  have h1 : (↑(1#u32) : Nat) = 1 := by simp
  have h1' : (↑(1#usize) : Nat) = 1 := by simp
  rw [UScalar.val_xor, UScalar.val_or, hr1, hrr, UScalar.val_and, hr2, hk1, h1, h1',
    UScalar.size_UScalarTyU32]
  exact parent_val_u32 v _ hk30 hchar

/-- A node value below `MAX_TREE_SIZE = 2^30` has its parent value below `2^30` too.  `BitMath`'s
    `parent_val_lt` only gives the `2^31` bound (enough for overflow-freedom); the `MAX_PARENT`
    range checks need the tighter `2^30` version, which is the same case split at `d = 29`. -/
private theorem parent_val_lt_two_pow_30 (V k : Nat) (hV : V < 2 ^ 30 - 1)
    (hk : V % 2 ^ (k + 1) = 2 ^ k - 1) :
    2 ^ (k + 2) * (V / 2 ^ (k + 2)) + (2 ^ (k + 1) - 1) < 2 ^ 30 := by
  -- `V < 2^30 − 1` is needed, not just `V < 2^30`: `V = 2^30 − 1` has `k = 30`, whose parent value
  -- is `2^31 − 1`.  Both callers have the strict bound (`2·l ≤ 2^30−2`, `2·p+1 ≤ 2^30−3`).
  have hle : 2 ^ k - 1 ≤ V := by rw [← hk]; exact Nat.mod_le _ _
  have h1 : 1 ≤ (2 : Nat) ^ k := Nat.one_le_two_pow
  rcases Nat.lt_or_ge k 29 with hlt | hge
  · refine parent_lt 29 k _ hlt ?_
    refine Nat.div_lt_of_lt_mul ?_
    rw [← pow_add, show (k + 2) + (29 - 1 - k) = 30 from by omega]
    omega
  · have hk29 : k = 29 := by
      by_contra hc
      have : (2 : Nat) ^ 30 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hk29
    have hq0 : V / 2 ^ (29 + 2) = 0 := by
      apply Nat.div_eq_of_lt
      have : (2 : Nat) ^ 30 ≤ 2 ^ (29 + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hq0, Nat.mul_zero, Nat.zero_add]
    have he : (2 : Nat) ^ (29 + 1) = 2 ^ 30 := by norm_num
    have h1' : 1 ≤ (2 : Nat) ^ (29 + 1) := Nat.one_le_two_pow
    omega

/-- Value-carrying spec for `parent` (user-validated exception; mirrors `level.spec_pure`).
    Registered `@[spec]`; the official `parent.spec.proof` is derived from it and unregistered.
    `v` is `x`'s tree index, `tones v` its trailing-ones count (BitMath); the parent's tree
    index is the classic formula. Planned Rust backport: ensures phrased via in-crate `level`
    (no `trailing_ones` — CoreModels lacks a model).

    NOT YET REGISTERED `@[spec]`.  The swap was attempted and reverted: with `spec_value` registered
    in place of `parent.spec.proof`, `sibling.spec.proof`'s blanket `scalar_tac` fails on 9 goals
    (it consumed parent's 3 clauses — bound, `MAX_ROOT_INDEX ∨ valid`, level successor — which the
    value equation implies but not syntactically), and `parent.spec.proof` itself hits a `simp`
    `maxRecDepth` in its `vc3.hQ` branch.  Next slice: do the swap together with re-deriving the
    three clauses for `sibling` (bound via `parent_val_lt_two_pow_30`, validity likewise, level via
    `tones_parent`/`trailing_unique`). -/
theorem parent.spec_value (x : TreeNodeIndex)
    (hx : match x with
          | .Leaf l => (↑l : Nat) ≤ 2^29 - 1
          | .Parent p => (↑p : Nat) ≤ 2^29 - 2) :
    ⦃ ⌜ True ⌝ ⦄
    parent x
    ⦃ ⇓ r => ⌜ 2 * (↑r : Nat) + 1 =
        (let v := match x with
                  | .Leaf l => 2 * (↑l : Nat)
                  | .Parent p => 2 * (↑p : Nat) + 1;
         2 ^ (tones v + 2) * (v / 2 ^ (tones v + 2)) + (2 ^ (tones v + 1) - 1)) ⌝ ⦄ := by
  -- `x` must be split BEFORE `mvcgen`: the dependent pure pre `hx` is a `match` on `x`, and the
  -- matcher splitter cannot lift it (motive type error).  No folded monadic hypothesis exists yet,
  -- so `cases x` is safe here.  After the split both branches present the SAME VC shapes, so the
  -- three residual scripts below are shared (each `case` tag occurs twice, `Leaf` then `Parent`).
  cases x
  all_goals dsimp only at hx ⊢
  all_goals hax_mvcgen [parent]
  -- `vc1.hidx` (`level.spec_pure`'s `< 2^30` pre) and every `h_fail` overflow branch are linear in
  -- `hx` plus the `level` characterization (`k + 1 ≤ 31 < 32 = numBits`).
  all_goals try scalar_tac
  -- `X = (v ||| 1<<<k) ^^^ ((v >>> (k+1)) &&& 1) <<< (k+1)` is positive: `parent_bits_val` turns it
  -- into `2^(k+2)·q + (2^(k+1) − 1) ≥ 2^(k+1) − 1 ≥ 1`.
  case vc2.h =>
    rename_i v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    have hge : 2 ^ ((↑k : Nat) + 1) - 1 ≤ (↑((v ||| r1) ^^^ rr) : Nat) := by
      rw [hval]; exact Nat.le_add_left _ _
    have h2 : (2 : Nat) ^ ((↑k : Nat) + 1) = 2 * 2 ^ (↑k : Nat) := by ring
    have h3 : 1 ≤ (2 : Nat) ^ (↑k : Nat) := Nat.one_le_two_pow
    have hpos : 0 < (↑((v ||| r1) ^^^ rr) : Nat) := by omega
    scalar_tac
  case vc2.h =>
    rename_i v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    have hge : 2 ^ ((↑k : Nat) + 1) - 1 ≤ (↑((v ||| r1) ^^^ rr) : Nat) := by
      rw [hval]; exact Nat.le_add_left _ _
    have h2 : (2 : Nat) ^ ((↑k : Nat) + 1) = 2 * 2 ^ (↑k : Nat) := by ring
    have h3 : 1 ≤ (2 : Nat) ^ (↑k : Nat) := Nat.one_le_two_pow
    have hpos : 0 < (↑((v ||| r1) ^^^ rr) : Nat) := by omega
    scalar_tac
  -- `X` is odd: `2 ∣ 2^(k+2)·q` and `2^(k+1) − 1` is odd.
  case vc3.h =>
    rename_i v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    have hdvd : 2 ∣ 2 ^ ((↑k : Nat) + 2) * ((↑v : Nat) / 2 ^ ((↑k : Nat) + 2)) :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    have h2 : (2 : Nat) ^ ((↑k : Nat) + 1) = 2 * 2 ^ (↑k : Nat) := by ring
    have h3 : 1 ≤ (2 : Nat) ^ (↑k : Nat) := Nat.one_le_two_pow
    have hodd : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by omega
    scalar_tac
  case vc3.h =>
    rename_i v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    have hdvd : 2 ∣ 2 ^ ((↑k : Nat) + 2) * ((↑v : Nat) / 2 ^ ((↑k : Nat) + 2)) :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    have h2 : (2 : Nat) ^ ((↑k : Nat) + 1) = 2 * 2 ^ (↑k : Nat) := by ring
    have h3 : 1 ≤ (2 : Nat) ^ (↑k : Nat) := Nat.one_le_two_pow
    have hodd : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by omega
    scalar_tac
  -- The value equation itself.  `trailing_unique` pins `k = tones ↑v` (both satisfy the same
  -- trailing-ones characterization), `parent_bits_val` is then literally the right-hand side, and
  -- `from_tree_index` returns `(X − 1)/2` with `X` odd — so `2·r + 1 = X`.  The `∀ V, V = ↑v →`
  -- wrapper is what makes the script constructor-agnostic: `V` is `2·l` resp. `2·p+1`, and the link
  -- to the loop variable `v` is linear (`scalar_tac`) in either shape.
  case vc4.hQ =>
    rename_i v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1 xm1 hxm1 hX1 dd hd
    have key : ∀ V : Nat, V = (↑v : Nat) →
        2 * (↑dd : Nat) + 1 =
          2 ^ (tones V + 2) * (V / 2 ^ (tones V + 2)) + (2 ^ (tones V + 1) - 1) := by
      intro V hV
      subst hV
      have e1 : (↑(1#u32) : Nat) = 1 := by simp
      have e2 : (↑(2#u32) : Nat) = 2 := by simp
      have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
      have hkt : (↑k : Nat) = tones (↑v : Nat) :=
        trailing_unique (↑v : Nat) (↑k : Nat) (tones (↑v : Nat)) hk.2 (tones_mod _)
      have hoddX : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by rw [hm1, e1, e2] at hm; omega
      rw [← hkt, ← hval]
      rw [e1] at hxm1 hX1
      rw [e2] at hd
      omega
    exact key _ (by scalar_tac)
  case vc4.hQ =>
    rename_i v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1 xm1 hxm1 hX1 dd hd
    have key : ∀ V : Nat, V = (↑v : Nat) →
        2 * (↑dd : Nat) + 1 =
          2 ^ (tones V + 2) * (V / 2 ^ (tones V + 2)) + (2 ^ (tones V + 1) - 1) := by
      intro V hV
      subst hV
      have e1 : (↑(1#u32) : Nat) = 1 := by simp
      have e2 : (↑(2#u32) : Nat) = 2 := by simp
      have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
      have hkt : (↑k : Nat) = tones (↑v : Nat) :=
        trailing_unique (↑v : Nat) (↑k : Nat) (tones (↑v : Nat)) hk.2 (tones_mod _)
      have hoddX : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by rw [hm1, e1, e2] at hm; omega
      rw [← hkt, ← hval]
      rw [e1] at hxm1 hX1
      rw [e2] at hd
      omega
    exact key _ (by scalar_tac)

@[spec]
theorem parent.spec.proof
  (x : TreeNodeIndex) :
  (parent.pre x).holds →
  ⦃ ⌜ True ⌝ ⦄
  parent x
  ⦃ ⇓ res =>
  ⌜ (parent.post x res).holds ⌝ ⦄
  := by
  -- The earlier draft unfolded `pre parent` up front, which left the post *folded* and blocked
  -- `hax_mvcgen` from stepping the registered `level` spec — hence the blow-up. Unfolding only
  -- `parent.pre`/`parent.post` keeps the level spec applicable and `scalar_tac` closes the rest.
  unfold parent.pre parent.post
  intro h_pre
  apply triple_in_hypothesis (h := h_pre)
  clear h_pre
  hax_mvcgen [parent]
  all_goals try scalar_tac
  -- Residue (both `x` constructors): the `level`-characterisation hypotheses are in scope and the
  -- remaining VCs are genuinely bitwise.  `parent_bits_val` turns the bit expression into
  -- `2^(k+2)·q + (2^(k+1) − 1)`, after which positivity and oddness are pure `Nat` arithmetic.
  -- `Leaf` branch --------------------------------------------------------------------------------
  case vc2.h =>
    rename_i v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    have hge : 2 ^ ((↑k : Nat) + 1) - 1 ≤ (↑((v ||| r1) ^^^ rr) : Nat) := by
      rw [hval]; exact Nat.le_add_left _ _
    have h2 : (2 : Nat) ^ ((↑k : Nat) + 1) = 2 * 2 ^ (↑k : Nat) := by ring
    have h3 : 1 ≤ (2 : Nat) ^ (↑k : Nat) := Nat.one_le_two_pow
    have hpos : 0 < (↑((v ||| r1) ^^^ rr) : Nat) := by omega
    scalar_tac
  case vc3.h =>
    rename_i v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u hposX m hm
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    have hdvd : 2 ∣ 2 ^ ((↑k : Nat) + 2) * ((↑v : Nat) / 2 ^ ((↑k : Nat) + 2)) :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    have h2 : (2 : Nat) ^ ((↑k : Nat) + 1) = 2 * 2 ^ (↑k : Nat) := by ring
    have h3 : 1 ≤ (2 : Nat) ^ (↑k : Nat) := Nat.one_le_two_pow
    have hodd : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by omega
    scalar_tac
  -- Level successor: `t2 = 2·((X−1)/2)+1 = X` (X is odd), so `tones t2 = k+1` by `tones_parent`,
  -- while `trailing_unique` pins both `level` results — `lvl2 = k+1 = lvl1+1`.
  case vc9.hQ =>
    rename_i v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1 xm1 hxm1 hX1
      d hd pidx hpidx bnd hbnd hple w hw hwne bb hbb hbbt t1 ht1 t2 ht2 lvl2 hlvl2 lvl1 hlvl1
      succ hsucc
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e1' : (↑(1#usize) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1 ht2
    rw [e2] at ht1 hd hv
    rw [e1'] at hsucc
    have hoddX : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by rw [hm1, e1, e2] at hm; omega
    have ht2v : (↑t2 : Nat) = (↑((v ||| r1) ^^^ rr) : Nat) := by omega
    have htn : tones (↑t2 : Nat) = (↑k : Nat) + 1 := by rw [ht2v, hval]; exact tones_parent _ _
    have hlvl2eq : (↑lvl2 : Nat) = (↑k : Nat) + 1 := by
      have := trailing_unique (↑t2 : Nat) (↑lvl2 : Nat) (tones (↑t2 : Nat)) hlvl2.2 (tones_mod _)
      omega
    have hwv : (↑w : Nat) = (↑v : Nat) := by omega
    rw [hwv] at hlvl1
    have hlvl1eq : (↑lvl1 : Nat) = (↑k : Nat) :=
      trailing_unique (↑v : Nat) (↑lvl1 : Nat) (↑k : Nat) hlvl1.2 hk.2
    exact decide_eq_true (UScalar.eq_of_val_eq (by omega))
  -- TODO(arith): the two `MAX_PARENT`/`MAX_TREE_INDEX` bound goals.  For a `Leaf`, `v = 2·l` is
  -- even so `tones v = 0` (`tones_even` + `trailing_unique`) and the parent value collapses to
  -- `4·(v/4) + 1`, giving `(X−1)/2 = 2·(v/4) ≤ 2^29−2` (it is even, so it cannot be `2^29−1`).
  case vc13.hQ =>
    rename_i bb0 hbb0 hbb0t l hx v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1
      xm1 hxm1 hX1 dd hd pidx hpidx bnd hbnd hple w hw hwne bb hbb hbbt
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    simp only [hx] at hbb0
    rw [hbb0] at hbb0t
    have hl : (↑l : Nat) ≤ 2 ^ 29 - 1 := of_decide_eq_true hbb0t
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1
    rw [e2] at hd hv
    -- `v = 2·l` is even, so its trailing-ones count is `0`; the parent value collapses to `4·(v/4)+1`.
    have hk0 : (↑k : Nat) = 0 :=
      (trailing_unique (↑v : Nat) 0 (↑k : Nat)
        (by simpa using (by omega : (↑v : Nat) % 2 = 0)) hk.2).symm
    have hXv : (↑((v ||| r1) ^^^ rr) : Nat) = 4 * ((↑v : Nat) / 4) + 1 := by
      rw [hval, hk0]; norm_num
    exact absurd (hbb.trans (decide_eq_true (by omega))) hbbt
  case vc15.hQ =>
    rename_i bb0 hbb0 hbb0t l hx v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1
      xm1 hxm1 hX1 dd hd pidx hpidx bnd hbnd hple
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    simp only [hx] at hbb0
    rw [hbb0] at hbb0t
    have hl : (↑l : Nat) ≤ 2 ^ 29 - 1 := of_decide_eq_true hbb0t
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1 hbnd
    rw [e2] at hd hv
    have hk0 : (↑k : Nat) = 0 :=
      (trailing_unique (↑v : Nat) 0 (↑k : Nat)
        (by simpa using (by omega : (↑v : Nat) % 2 = 0)) hk.2).symm
    have hXv : (↑((v ||| r1) ^^^ rr) : Nat) = 4 * ((↑v : Nat) / 4) + 1 := by
      rw [hval, hk0]; norm_num
    have hb : (↑(536870910#u32) : Nat) = 536870910 := by simp
    rw [hb] at hbnd
    exact absurd ((UScalar.le_equiv pidx bnd).2 (by omega)) hple
  -- `Parent` branch ------------------------------------------------------------------------------
  case vc14.h =>
    rename_i v0 hv0 v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    have hge : 2 ^ ((↑k : Nat) + 1) - 1 ≤ (↑((v ||| r1) ^^^ rr) : Nat) := by
      rw [hval]; exact Nat.le_add_left _ _
    have h2 : (2 : Nat) ^ ((↑k : Nat) + 1) = 2 * 2 ^ (↑k : Nat) := by ring
    have h3 : 1 ≤ (2 : Nat) ^ (↑k : Nat) := Nat.one_le_two_pow
    have hpos : 0 < (↑((v ||| r1) ^^^ rr) : Nat) := by omega
    scalar_tac
  case vc15.h =>
    rename_i v0 hv0 v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u hposX m hm
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    have hdvd : 2 ∣ 2 ^ ((↑k : Nat) + 2) * ((↑v : Nat) / 2 ^ ((↑k : Nat) + 2)) :=
      Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    have h2 : (2 : Nat) ^ ((↑k : Nat) + 1) = 2 * 2 ^ (↑k : Nat) := by ring
    have h3 : 1 ≤ (2 : Nat) ^ (↑k : Nat) := Nat.one_le_two_pow
    have hodd : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by omega
    scalar_tac
  -- Same level-successor argument; the `Parent` shape adds the `2·p+1` step and splits on the
  -- `x == MAX_TREE_INDEX` test, giving two copies of the obligation.
  case vc3.hQ =>
    rename_i v0 hv0 v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1 xm1 hxm1 hX1
      d hd pidx hpidx bnd hbnd hple w hw hweq t1 ht1 t2 ht2 lvl2 hlvl2 lvl1 hlvl1 succ hsucc
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e1' : (↑(1#usize) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1 ht2 hv
    rw [e2] at ht1 hd hv0
    rw [e1'] at hsucc
    have hoddX : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by rw [hm1, e1, e2] at hm; omega
    have ht2v : (↑t2 : Nat) = (↑((v ||| r1) ^^^ rr) : Nat) := by omega
    have htn : tones (↑t2 : Nat) = (↑k : Nat) + 1 := by rw [ht2v, hval]; exact tones_parent _ _
    have hlvl2eq : (↑lvl2 : Nat) = (↑k : Nat) + 1 := by
      have := trailing_unique (↑t2 : Nat) (↑lvl2 : Nat) (tones (↑t2 : Nat)) hlvl2.2 (tones_mod _)
      omega
    have hwv : (↑w : Nat) = (↑v : Nat) := by omega
    rw [hwv] at hlvl1
    have hlvl1eq : (↑lvl1 : Nat) = (↑k : Nat) :=
      trailing_unique (↑v : Nat) (↑lvl1 : Nat) (↑k : Nat) hlvl1.2 hk.2
    exact decide_eq_true (UScalar.eq_of_val_eq (by omega))
  case vc9.hQ =>
    rename_i v0 hv0 v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1 xm1 hxm1 hX1
      d hd pidx hpidx bnd hbnd hple w hw hwne bb hbb hbbt t1 ht1 t2 ht2 lvl2 hlvl2 lvl1 hlvl1
      succ hsucc
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e1' : (↑(1#usize) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1 ht2 hv
    rw [e2] at ht1 hd hv0
    rw [e1'] at hsucc
    have hoddX : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by rw [hm1, e1, e2] at hm; omega
    have ht2v : (↑t2 : Nat) = (↑((v ||| r1) ^^^ rr) : Nat) := by omega
    have htn : tones (↑t2 : Nat) = (↑k : Nat) + 1 := by rw [ht2v, hval]; exact tones_parent _ _
    have hlvl2eq : (↑lvl2 : Nat) = (↑k : Nat) + 1 := by
      have := trailing_unique (↑t2 : Nat) (↑lvl2 : Nat) (tones (↑t2 : Nat)) hlvl2.2 (tones_mod _)
      omega
    have hwv : (↑w : Nat) = (↑v : Nat) := by omega
    rw [hwv] at hlvl1
    have hlvl1eq : (↑lvl1 : Nat) = (↑k : Nat) :=
      trailing_unique (↑v : Nat) (↑lvl1 : Nat) (↑k : Nat) hlvl1.2 hk.2
    exact decide_eq_true (UScalar.eq_of_val_eq (by omega))
  -- TODO(arith): the `Parent` bound goals.  Here `v = 2·p+1` is odd so `k = tones v ≥ 1` is not
  -- pinned; the argument is `k ≤ 29` (from `2^k − 1 ≤ v < 2^30`) then `parent_lt 29 k q` for
  -- `k ≤ 28`, with `k = 29` forcing `v = 2^29−1` — excluded for `vc13` by the `x ≠ MAX_TREE_INDEX`
  -- hypothesis, and giving `X = 2^30−1`, `(X−1)/2 = 2^29−1` for `vc15`.
  case vc13.hQ =>
    rename_i bb0 hbb0 hbb0t p hx v0 hv0 v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1
      xm1 hxm1 hX1 dd hd pidx hpidx bnd hbnd hple w hw hwne bb hbb hbbt
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    have hb2 : (↑(536870911#u32) : Nat) = 536870911 := by simp
    simp only [hx] at hbb0
    rw [hbb0] at hbb0t
    have hp : (↑p : Nat) ≤ 2 ^ 29 - 2 := of_decide_eq_true hbb0t
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1 hv
    rw [e2] at hd hv0
    have hoddX : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by rw [hm1, e1, e2] at hm; omega
    have hvlt : (↑v : Nat) < 2 ^ 30 - 1 := by omega
    have hXlt := parent_val_lt_two_pow_30 (↑v : Nat) (↑k : Nat) hvlt hk.2
    rw [← hval] at hXlt
    -- `dd = 2^29−1` would force `X = 2^30−1`, hence `tones X = 30 = k+1`, hence `v = 2^29−1` —
    -- exactly the `x ≠ MAX_TREE_INDEX` case the caller already ruled out.
    have hne : (↑dd : Nat) ≠ 2 ^ 29 - 1 := by
      intro hdd
      have hXeq : (↑((v ||| r1) ^^^ rr) : Nat) = 2 ^ 30 - 1 := by omega
      have h30 : tones ((↑((v ||| r1) ^^^ rr)) : Nat) = 30 := by
        rw [hXeq]; exact tones_pow_sub_one 30
      have hkp : tones ((↑((v ||| r1) ^^^ rr)) : Nat) = (↑k : Nat) + 1 := by
        rw [hval]; exact tones_parent _ _
      have hkeq : (↑k : Nat) = 29 := by omega
      have h2 := hk.2
      rw [hkeq] at h2
      norm_num at h2
      exact hwne (UScalar.eq_of_val_eq (by omega))
    exact absurd (hbb.trans (decide_eq_true (by omega))) hbbt
  case vc15.hQ =>
    rename_i bb0 hbb0 hbb0t p hx v0 hv0 v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1
      xm1 hxm1 hX1 dd hd pidx hpidx bnd hbnd hple
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    have hb : (↑(536870910#u32) : Nat) = 536870910 := by simp
    simp only [hx] at hbb0
    rw [hbb0] at hbb0t
    have hp : (↑p : Nat) ≤ 2 ^ 29 - 2 := of_decide_eq_true hbb0t
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1 hv hbnd
    rw [e2] at hd hv0
    rw [hb] at hbnd
    have hvlt : (↑v : Nat) < 2 ^ 30 - 1 := by omega
    have hXlt := parent_val_lt_two_pow_30 (↑v : Nat) (↑k : Nat) hvlt hk.2
    rw [← hval] at hXlt
    exact absurd ((UScalar.le_equiv pidx bnd).2 (by omega)) hple

@[spec]
theorem sibling.spec.proof
  (index : TreeNodeIndex) :
  (sibling.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄
  sibling index
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  -- The post is `True`, so this is pure panic-freedom: `parent` must not overflow, and the
  -- `left`/`right` calls that follow must meet their `ParentNodeIndex.valid` pres.
  --
  -- Same shape as `parent.spec.proof`: unfold ONLY `sibling.pre` (leaving the callees' specs
  -- applicable), turn the pre into hypotheses with `triple_in_hypothesis`, then `hax_mvcgen`.
  --
  -- The key discharge comes from the now-proved `parent.spec.proof`: its post arrives as a
  -- hypothesis `(parent.post index p).holds`, which `hax_mvcgen` decomposes along its three
  -- clauses.  Clause 1 (`↑p ≤ MAX_PARENT + 1`) is what bounds `p.to_tree_index = 2·p + 1` below
  -- `2^30`, discharging both `ParentNodeIndex.to_tree_index`'s side conditions and the `level`
  -- side conditions (`hidx : ↑r < 2^30`) that clause 3 drags in.  Clause 2
  -- (`index.u32 = MAX_ROOT_INDEX ∨ p.valid`) combines with the pre's `index.u32 ≠ MAX_ROOT_INDEX`
  -- to give `p.valid` — i.e. `↑p ≤ 2^29 - 2` — which is exactly `left.pre`/`right.pre`.
  --
  -- All of that is linear once the clauses are in scope, so a blanket `scalar_tac` suffices; note
  -- `cases index <;> simp_all` must NOT be used here (it substitutes into the still-folded
  -- `parent.post` hypothesis and blows the heartbeat budget on `whnf`).
  unfold sibling.pre
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [sibling]
  all_goals scalar_tac

/-! ### `direct_path`: the on-path walk

    BLOCKER (recorded for the next slice).  The invariant below is the right one, but the step is
    **not** provable from the *registered* postcondition of `parent`.  `parent.post` exposes only
    three clauses — `↑p ≤ MAX_PARENT + 1`, `x.u32 = MAX_ROOT_INDEX ∨ p.valid`, and the level
    successor `level (2·p+1) = level x.u32 + 1` — and *no relation between the values* of `x` and
    `p`.  Every remaining obligation of the step needs one:

    * `↑x1 < ↑size` for `x1 = 2·p+1` (the walk must stay inside the tree).  This is also the only
      way to rule out `↑x = MAX_ROOT_INDEX = 2^29−1` for a non-root on-path `x`: with
      `tones ↑x ≤ L` and `↑x < ↑size` such an `x` forces `L = 29` and then `↑x = 2^L − 1 = ↑r`,
      excluded by the loop guard.  Without it `parent.pre` fails on the *next* iteration, so this
      is a genuine panic-freedom obligation, not just a functional one.
    * the per-entry bound `↑p < parent_count size = ↑size / 2`, i.e. `2·↑p + 1 < ↑size`
      (`2·↑p+1 = ↑size` is impossible: it would give `tones = L+1`).

    The missing ingredient is the value equation
    `2·↑p + 1 = 2^(k+2)·(↑x / 2^(k+2)) + (2^(k+1) − 1)` with `k = tones ↑x` — i.e. exactly
    `parent_bits_val`, but delivered *inside a triple for* `parent`.  Next slice: add
    `parent_value_spec` (unfold `parent`, step `level.spec_pure`, re-assemble with
    `parent_bits_val`, then `ParentNodeIndex.from_tree_index`), after which the loop lemma closes
    on the three arithmetic lemmas proved just below plus `tones_parent` / `trailing_unique`. -/

/-- On-path uniqueness: a value below `2^(L+1)` whose trailing-ones count is exactly `L` *is* the
    root value `2^L − 1` (`v % 2^(L+1) = v` when `v < 2^(L+1)`). -/
private theorem eq_root_of_tones_eq (v L : Nat) (hv : v < 2 ^ (L + 1)) (ht : tones v = L) :
    v = 2 ^ L - 1 := by
  have hm := tones_mod v
  rw [ht] at hm
  rwa [Nat.mod_eq_of_lt hv] at hm

/-- Below the root there is room left in the measure: an on-path `v` strictly inside the tree
    (`v < 2^(L+1) − 1`) that is not the root value has `tones v < L`. -/
private theorem tones_lt_of_ne_root (v L : Nat) (hv : v < 2 ^ (L + 1) - 1)
    (ht : tones v ≤ L) (hne : v ≠ 2 ^ L - 1) : tones v < L := by
  rcases Nat.lt_or_ge (tones v) L with h | h
  · exact h
  · exact absurd (eq_root_of_tones_eq v L (by omega) (by omega)) hne

/-- The parent value of an on-path node stays strictly inside the tree: with `size = 2^(L+1) − 1`,
    `k = tones x < L` and `x < size`, the parent value `2^(k+2)·(x / 2^(k+2)) + (2^(k+1) − 1)` is
    `< size`.  `parent_lt` gives `< 2^(L+1)`; equality with `2^(L+1) − 1` is excluded because that
    value has `L+1` trailing ones while the parent value has `k+1 ≤ L`. -/
private theorem parent_val_lt_size (x L k : Nat) (hL : k < L) (hx : x < 2 ^ (L + 1) - 1) :
    2 ^ (k + 2) * (x / 2 ^ (k + 2)) + (2 ^ (k + 1) - 1) < 2 ^ (L + 1) - 1 := by
  have hlt : 2 ^ (k + 2) * (x / 2 ^ (k + 2)) + (2 ^ (k + 1) - 1) < 2 ^ (L + 1) := by
    refine parent_lt L k _ hL ?_
    refine Nat.div_lt_of_lt_mul ?_
    rw [← pow_add, show (k + 2) + (L - 1 - k) = L + 1 from by omega]
    omega
  have htp : tones (2 ^ (k + 2) * (x / 2 ^ (k + 2)) + (2 ^ (k + 1) - 1)) = k + 1 :=
    tones_parent _ _
  by_contra hc
  have heq : 2 ^ (k + 2) * (x / 2 ^ (k + 2)) + (2 ^ (k + 1) - 1) = 2 ^ (L + 1) - 1 := by omega
  rw [heq, tones_pow_sub_one] at htp
  omega

/-- Loop invariant for `direct_path_loop`, on the state `(d, x)`, with `s = ↑size = 2^(L+1) − 1`
    and root value `↑r = 2^L − 1`:

    * `↑x < s` — `x` is a tree index inside the tree;
    * `tones ↑x ≤ L` — `x` sits on the direct path (its level does not exceed the root's);
    * `vecLen d = tones ↑x` — the number of parents collected so far is exactly the level of `x`
      (it starts at `tones (2·node_index) = 0` and both sides grow by one per step), which is what
      yields the postcondition's `len ≤ 30`;
    * every collected parent is `valid` and inside the tree — the two per-entry clauses of
      `direct_path.post`.

    The measure is `L − tones ↑x`: `parent`'s level-successor clause makes `tones` grow by one per
    iteration, and `tones_lt_of_ne_root` turns the loop guard `x ≠ r` into `tones ↑x < L`. -/
def direct_path_loop_inv (s L : Nat)
    (p : alloc.vec.Vec ParentNodeIndex × Std.U32) : Prop :=
  (↑p.2 : Nat) < s ∧ tones (↑p.2 : Nat) ≤ L
  ∧ vecLen p.1 = tones (↑p.2 : Nat)
  ∧ ∀ e ∈ p.1.1, (↑e : Nat) ≤ 2 ^ 29 - 2 ∧ 2 * (↑e : Nat) + 1 < s

/-! ### `direct_path`: status of the two halves

    1. **The loop is DONE** — `direct_path_loop_spec` just below.  Recorded because it cost a slice
       to find: the value-carrying `parent.spec_value` will *not* fire from the `mvcgen` list (the
       globally registered three-clause `parent.spec.proof` wins, and the VCs arrive carrying
       `(parent.post …).holds`), and a section-local `attribute [local spec] parent.spec_value` does
       not override it either — both measured.  What works is `mvcgen`'s simp-style *erasure*
       `- parent.spec.proof`, which is scoped to the single call, so the global registration that
       `sibling.spec.proof` and `parent.spec.proof` depend on is untouched: **the registration swap
       the old blocker note called for is NOT needed.**

    2. **`direct_path.spec.proof` is blocked on the admitted surface, not on maths.**  Its post is
       index-based (`∀ i < len, (index result i …).holds`) and `AdmittedCoreSpecs.vec_index_spec`
       has postcondition `⌜ True ⌝` — it delivers no relation between the indexed result and the
       vector.  So the two `∀ i < len` clauses cannot be discharged from the membership-flavoured
       invariant, no matter how the loop lemma is phrased.  USER DECISION NEEDED: strengthen
       `vec_index_spec` to a value-carrying contract (`result = v.1[i]`) on the trusted surface, or
       leave `direct_path.spec.proof` sorried.  (Not added here: the admitted surface is not the
       proof agent's to extend.) -/

/-- The `direct_path` walk: from an on-path node `x` inside the tree, repeatedly replace `x` by its
    parent until the root value `↑r = 2^L − 1` is reached, collecting the parents.  On exit the
    collected vector has length exactly `L` (`= tones ↑r`, so `≤ 29`) and every entry is `valid`
    (`≤ 2^29 − 2`) and inside the tree (`2·e + 1 < s`) — i.e. exactly the two per-entry clauses of
    `direct_path.post`, in membership form.

    The step runs on `parent.spec_value`, forced past the globally registered three-clause
    `parent.spec.proof` by `mvcgen`'s simp-style erasure `- parent.spec.proof` (see the note above:
    neither a plain list entry nor a section-local `@[spec]` overrides it).  With `k = tones ↑x` it
    gives `2·↑p + 1 = 2^(k+2)·(↑x / 2^(k+2)) + (2^(k+1) − 1)`; `parent_val_lt_size` keeps that value
    `< s`, `tones_parent` raises `tones` by exactly one (so the measure `L − tones ↑x` drops and
    `vecLen d = tones ↑x` is maintained), and `2·↑p + 1 < s ≤ 2^30 − 1` yields `↑p ≤ 2^29 − 2` for
    the freshly pushed entry.  `TreeNodeIndex.new` and both `from_tree_index` are unfolded (their
    registered specs are value-less), which is what exposes `2·(↑x/2) = ↑x` (even) resp.
    `2·((↑x−1)/2) + 1 = ↑x` (odd) — the link from `spec_value`'s `v` to `↑x` in each parity. -/
@[spec]
theorem direct_path_loop_spec (s L : Nat) (r : Std.U32)
    (d : alloc.vec.Vec ParentNodeIndex) (x : Std.U32)
    (hs : s = 2 ^ (L + 1) - 1) (hL : L ≤ 29) (hr : (↑r : Nat) = 2 ^ L - 1)
    (hinv : direct_path_loop_inv s L (d, x)) :
    ⦃ ⌜ True ⌝ ⦄
    direct_path_loop r d x
    ⦃ ⇓ res => ⌜ vecLen res = L
        ∧ ∀ e ∈ res.1, (↑e : Nat) ≤ 2 ^ 29 - 2 ∧ 2 * (↑e : Nat) + 1 < s ⌝ ⦄ := by
  -- Numeric shape of the tree size, in numerals: the `2 ^ L` atoms stay out of `scalar_tac`'s way.
  have hp1 : (1 : Nat) ≤ 2 ^ L := Nat.one_le_two_pow
  have hpL : (2 : Nat) ^ L ≤ 2 ^ 29 := Nat.pow_le_pow_right (by norm_num) hL
  have hpS : (2 : Nat) ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have hsnum : s ≤ 1073741823 := by simp only [hs]; omega
  unfold direct_path_loop
  apply loop_spec_measure
    (measure := fun p => L - tones (↑p.2 : Nat))
    (inv := direct_path_loop_inv s L)
    -- The `Vec ParentNodeIndex` ascription is REQUIRED: without it `β` is inferred as `Vec ℕ` from
    -- the `↑e` coercion and `apply` fails to unify.
    (post := fun (res : alloc.vec.Vec ParentNodeIndex) => vecLen res = L
        ∧ ∀ e ∈ res.1, (↑e : Nat) ≤ 2 ^ 29 - 2 ∧ 2 * (↑e : Nat) + 1 < s)
  · exact hinv
  · rintro ⟨dd, xx⟩ hI
    obtain ⟨hxs, hxt, hlen, hents⟩ := hI
    simp only at hxs hxt hlen hents ⊢
    unfold direct_path_loop.body
    split
    · -- `xx ≠ r`: one more step up the path.
      rename_i hne
      have hxr : (↑xx : Nat) ≠ 2 ^ L - 1 := by
        intro h
        exact absurd (by scalar_tac : xx = r) (by simpa [bne_iff_ne] using hne)
      have hklt : tones (↑xx : Nat) < L := tones_lt_of_ne_root _ L (by omega) hxt hxr
      have hxnum : (↑xx : Nat) ≤ 1073741822 := by omega
      have hPlt : 2 ^ (tones (↑xx : Nat) + 2) * ((↑xx : Nat) / 2 ^ (tones (↑xx : Nat) + 2))
          + (2 ^ (tones (↑xx : Nat) + 1) - 1) < s := by
        rw [hs]; exact parent_val_lt_size _ L _ hklt (by omega)
      have hlen29 : vecLen dd ≤ 29 := by omega
      have h2u : ((2#u32 : Std.U32) : Nat) = 2 := by simp
      have h1u : ((1#u32 : Std.U32) : Nat) = 1 := by simp
      -- `- parent.spec.proof` (local to this call) is what lets `parent.spec_value` fire.
      mvcgen [parent.spec_value, - parent.spec.proof, TreeNodeIndex.new,
        LeafNodeIndex.from_tree_index, ParentNodeIndex.from_tree_index, vec_push_spec]
      -- Even `xx`: the step maintains the invariant and drops the measure.
      case vc4.hQ =>
        rename_i b2 hb2e u1 hb2 half hhalf p hval d1 hd1 x1 hx1
        have heven : (↑xx : Nat) % 2 = 0 := by simpa using hb2e ▸ hb2
        have hv : 2 * (↑half : Nat) = (↑xx : Nat) := by rw [hhalf, h2u]; omega
        rw [hv] at hval
        obtain ⟨hlen1, hlist⟩ := hd1
        have hx1s : (↑x1 : Nat) < s := by rw [hx1, hval]; exact hPlt
        have htn : tones (↑x1 : Nat) = tones (↑xx : Nat) + 1 := by
          rw [hx1, hval]; exact tones_parent _ _
        have hple : (↑p : Nat) ≤ 2 ^ 29 - 2 := by omega
        refine ⟨?_, by omega⟩
        simp only [direct_path_loop_inv]
        refine ⟨hx1s, by omega, ?_, ?_⟩
        · rw [hlen1, hlen, htn]
        · rw [hlist]
          intro e he
          rcases List.mem_append.1 he with h | h
          · exact hents e h
          · simp only [List.mem_singleton] at h
            subst h
            exact ⟨hple, by omega⟩
      -- Odd `xx`: same, with `2·((↑xx − 1)/2) + 1 = ↑xx`.
      case vc11.hQ =>
        rename_i m hm u2 hm1 xm1 hxm1 hxge1 half hhalf p hval d1 hd1 x1 hx1
        have hodd : (↑xx : Nat) % 2 = 1 := by
          have hm1' : (↑m : Nat) = 1 := by rw [hm1]; simp
          rw [hm, h2u] at hm1'; exact hm1'
        have hv : 2 * (↑half : Nat) + 1 = (↑xx : Nat) := by
          rw [hhalf, hxm1, h1u, h2u]; omega
        rw [hv] at hval
        obtain ⟨hlen1, hlist⟩ := hd1
        have hx1s : (↑x1 : Nat) < s := by rw [hx1, hval]; exact hPlt
        have htn : tones (↑x1 : Nat) = tones (↑xx : Nat) + 1 := by
          rw [hx1, hval]; exact tones_parent _ _
        have hple : (↑p : Nat) ≤ 2 ^ 29 - 2 := by omega
        refine ⟨?_, by omega⟩
        simp only [direct_path_loop_inv]
        refine ⟨hx1s, by omega, ?_, ?_⟩
        · rw [hlen1, hlen, htn]
        · rw [hlist]
          intro e he
          rcases List.mem_append.1 he with h | h
          · exact hents e h
          · simp only [List.mem_singleton] at h
            subst h
            exact ⟨hple, by omega⟩
      -- `to_tree_index`'s `2·p + 1` cannot overflow: the value equation plus `parent_val_lt_size`
      -- bound it by `s ≤ 2^30 − 1`.  Even, then odd branch.
      case vc5.h_fail =>
        rename_i b2 hb2e u1 hb2 half hhalf p hval d1 hd1 hof
        have heven : (↑xx : Nat) % 2 = 0 := by simpa using hb2e ▸ hb2
        have hv : 2 * (↑half : Nat) = (↑xx : Nat) := by rw [hhalf, h2u]; omega
        rw [hv] at hval
        have hlt : 2 * (↑p : Nat) + 1 < s := by rw [hval]; exact hPlt
        scalar_tac
      case vc12.h_fail =>
        rename_i m hm u2 hm1 xm1 hxm1 hxge1 half hhalf p hval d1 hd1 hof
        have hodd : (↑xx : Nat) % 2 = 1 := by
          have hm1' : (↑m : Nat) = 1 := by rw [hm1]; simp
          rw [hm, h2u] at hm1'; exact hm1'
        have hv : 2 * (↑half : Nat) + 1 = (↑xx : Nat) := by
          rw [hhalf, hxm1, h1u, h2u]; omega
        rw [hv] at hval
        have hlt : 2 * (↑p : Nat) + 1 < s := by rw [hval]; exact hPlt
        scalar_tac
      -- Residue: the two `spec_value` payload bounds (`↑xx/2 ≤ 2^29−1`, `(↑xx−1)/2 ≤ 2^29−2`), the
      -- `push` capacity, the parity massertions and the `↑xx − 1` underflow guard — all linear in
      -- `hxnum` / `hlen29` plus the parity facts.
      all_goals scalar_tac
    · -- `xx = r`: done, and `vecLen dd = tones ↑r = L` by `tones_pow_sub_one`.
      rename_i heq
      have hxr : (↑xx : Nat) = 2 ^ L - 1 := by
        have h : (↑xx : Nat) = (↑r : Nat) := by simpa [bne_iff_ne] using heq
        rw [h, hr]
      mvcgen
      refine ⟨?_, hents⟩
      rw [hlen, hxr, tones_pow_sub_one]

@[spec]
theorem direct_path.spec.proof (node_index : LeafNodeIndex) (size : TreeSize) :
  (direct_path.pre node_index size).holds →
  ⦃ ⌜ True ⌝ ⦄
  direct_path node_index size
  ⦃ ⇓ res => ⌜ (direct_path.post node_index size res).holds ⌝ ⦄
  := by
  intros
  mvcgen [direct_path] <;> try scalar_tac
  all_goals sorry

@[spec]
theorem copath.spec.proof (leaf_index : LeafNodeIndex) (size : TreeSize) :
  (copath.pre leaf_index size).holds →
  ⦃ ⌜ True ⌝ ⦄ copath leaf_index size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  hax_mvcgen [copath]
  all_goals sorry

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

/-- `level`'s postcondition `v % 2^(k+1) = 2^k − 1` forces `k = 0` on an *even* `v`: for `k ≥ 1`
    the right-hand side is odd while the left-hand side inherits `v`'s parity. -/
private theorem level_res_eq_zero {v k : Nat} (hv : v % 2 = 0)
    (hmod : v % 2 ^ (k + 1) = 2 ^ k - 1) : k = 0 := by
  by_contra hk
  have h2dvd : (2 : Nat) ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
  have hk2 : (2 : Nat) ∣ 2 ^ k := dvd_pow_self 2 hk
  have h2le : (2 : Nat) ≤ 2 ^ k := by
    calc (2 : Nat) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmm : v % 2 ^ (k + 1) % 2 = v % 2 := Nat.mod_mod_of_dvd v h2dvd
  rw [hmod, hv] at hmm
  omega

/-- On a tree index `xv = 2·xn` the `level` call returns `0`, so the `k+1` shift amount that
    `lowest_common_ancestor` compares is exactly `1` and shifting by it recovers the leaf index
    `xn`. This is what makes all early-return branches unreachable: both tests degenerate to
    `xn = yn`, which the precondition rules out. -/
private theorem lca_level_one {xn : Nat} {xv : Std.U32} {k k1 : Std.Usize}
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

@[spec]
theorem lowest_common_ancestor.spec.proof (x : LeafNodeIndex) (y : LeafNodeIndex) :
  (lowest_common_ancestor.pre x y).holds →
  ⦃ ⌜ True ⌝ ⦄ lowest_common_ancestor x y ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  -- The precondition forces two distinct valid (`< 2^29`) leaves. Their tree-indices are even,
  -- so `level` returns `0` and both early-return branches are unreachable (their `x>>1 = y>>1`
  -- tests fail). Only the shift-loop runs; close its `from_tree_index` tail via `lca_tail_aux`.
  unfold lowest_common_ancestor.pre LeafNodeIndex.valid LeafNodeIndex.u32
  intro h_pre
  apply triple_in_hypothesis (h := h_pre)
  clear h_pre
  mvcgen ; simp
  -- (tags renumbered by the registered `@[spec]`s: the two unreachable `false = true → …`
  -- early-return branches are now `vc2.hQ` (`x` valid, `y` invalid) and `vc3.hQ` (`x` invalid);
  -- `vc1.hQ` is the real body (`¬ x = y → triple`) and is left for the script below.)
  case vc2.hQ =>
    grind
  case vc3.hQ =>
    grind
  simp_all; intro
  hax_mvcgen [lowest_common_ancestor]
  all_goals try scalar_tac
  -- Remaining vcs split in two families.
  --
  -- (a) `vc3/vc4/vc9/vc10/vc36/vc39/vc40/vc45` — the early-return branches. `lca_level_one`
  --     turns each `level` result into `k+1 = 1`, so every shift is by `1`; the branch tests
  --     then say either `xn = yn` (contradicting the pre) or compare two equal shift amounts.
  --
  -- (b) `vc20/vc21/vc26/vc27` — the `(xn <<< k) + (1 <<< (k−1)) − 1` tail after `loop0`,
  --     discharged from `lca_tail_aux` (sum `< 2^32`, both summands even, `1 <<< (k−1) ≥ 2`).
  case vc3.h =>
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hle sx hsx sy hsy heq
    exfalso
    obtain ⟨hkx1', hxs⟩ := lca_level_one hxv hkx hkx1
    obtain ⟨hky1', hys⟩ := lca_level_one hyv hky hky1
    rw [hkx1'] at hxs ; rw [hky1'] at hys
    have hval : (↑sx : Nat) = ↑sy := by rw [heq]
    rw [hsx, hsy, hky1', hxs, hys] at hval
    exact hxy hval
  case vc4.h =>
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hle sx hsx sy hsy heq
      u hpos m hm
    exfalso
    obtain ⟨hkx1', hxs⟩ := lca_level_one hxv hkx hkx1
    obtain ⟨hky1', hys⟩ := lca_level_one hyv hky hky1
    rw [hkx1'] at hxs ; rw [hky1'] at hys
    have hval : (↑sx : Nat) = ↑sy := by rw [heq]
    rw [hsx, hsy, hky1', hxs, hys] at hval
    exact hxy hval
  case vc9.h =>
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hle sx hsx sy hsy hne
      hle2 tx htx ty hty heq
    exfalso
    obtain ⟨hkx1', hxs⟩ := lca_level_one hxv hkx hkx1
    obtain ⟨hky1', hys⟩ := lca_level_one hyv hky hky1
    rw [hkx1'] at hxs ; rw [hky1'] at hys
    have hval : (↑tx : Nat) = ↑ty := by rw [heq]
    rw [htx, hty, hkx1', hxs, hys] at hval
    exact hxy hval
  case vc10.h =>
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hle sx hsx sy hsy hne
      hle2 tx htx ty hty heq u hpos m hm
    exfalso
    obtain ⟨hkx1', hxs⟩ := lca_level_one hxv hkx hkx1
    obtain ⟨hky1', hys⟩ := lca_level_one hyv hky hky1
    rw [hkx1'] at hxs ; rw [hky1'] at hys
    have hval : (↑tx : Nat) = ↑ty := by rw [heq]
    rw [htx, hty, hkx1', hxs, hys] at hval
    exact hxy hval
  case vc36.h_ok.isFalse.isFalse =>
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hle sx hsx sy hsy hne hnle
    exfalso
    have hkx1' := (lca_level_one hxv hkx hkx1).1
    have hky1' := (lca_level_one hyv hky hky1).1
    clear hkx hky hxv hyv hsx hsy hne hle hx hy hxy
    exact hnle (by scalar_tac)
  case vc39.h =>
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hnle hle sx hsx sy hsy heq
    exfalso
    have hkx1' := (lca_level_one hxv hkx hkx1).1
    have hky1' := (lca_level_one hyv hky hky1).1
    clear hkx hky hxv hyv hsx hsy heq hle hx hy hxy
    exact hnle (by scalar_tac)
  case vc40.h =>
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hnle hle sx hsx sy hsy heq
      u hpos m hm
    exfalso
    have hkx1' := (lca_level_one hxv hkx hkx1).1
    have hky1' := (lca_level_one hyv hky hky1).1
    clear hkx hky hxv hyv hsx hsy heq hle hx hy hxy hm hpos
    exact hnle (by scalar_tac)
  case vc45.h_ok.isFalse =>
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hnle hle sx hsx sy hsy hne
    exfalso
    have hkx1' := (lca_level_one hxv hkx hkx1).1
    have hky1' := (lca_level_one hyv hky hky1).1
    clear hkx hky hxv hyv hsx hsy hne hle hx hy hxy
    exact hnle (by scalar_tac)
  -- Family (b). In each block the `2 ^ …`-laden `level`/`loop0` hypotheses are cleared before
  -- `scalar_tac`, which otherwise diverges on them (see `Common.lean`).
  case vc20.h =>
    -- `i10 = i6 + i8 − 1 > 0` because `i8 = 1 <<< (k−1) ≥ 2`.
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hle sx hsx sy hsy hne
      hle2 tx htx ty hty hne2 p hp i6 hi6 i7 hi7 i8 hi8 i9 hi9 i10 hi10 hge
    obtain ⟨hk2, hk30, hbnd⟩ := hp
    obtain ⟨-, -, hi8ge, -⟩ := lca_tail_aux hk2 hk30 hbnd hi6 hi7 hi8
    clear hkx hky hxv hyv hsx hsy htx hty hbnd hi6 hi7 hi8 hk2 hk30
    scalar_tac
  case vc21.h =>
    -- `i10 = i6 + i8 − 1` is odd: `i6 = xn <<< k` and `i8 = 1 <<< (k−1)` are both even (`k ≥ 2`).
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hle sx hsx sy hsy hne
      hle2 tx htx ty hty hne2 p hp i6 hi6 i7 hi7 i8 hi8 i9 hi9 i10 hi10 hge u hpos m hm
    obtain ⟨hk2, hk30, hbnd⟩ := hp
    obtain ⟨-, hi6ev, hi8ge, hi8ev⟩ := lca_tail_aux hk2 hk30 hbnd hi6 hi7 hi8
    clear hkx hky hxv hyv hsx hsy htx hty hbnd hi6 hi7 hi8 hk2 hk30
    scalar_tac
  case vc26.h_fail =>
    -- The `i9 − 1` subtraction cannot underflow: `i9 = i6 + i8 ≥ 2`.
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hle sx hsx sy hsy hne
      hle2 tx htx ty hty hne2 p hp i6 hi6 i7 hi7 i8 hi8 i9 hi9 hlt
    obtain ⟨hk2, hk30, hbnd⟩ := hp
    obtain ⟨-, -, hi8ge, -⟩ := lca_tail_aux hk2 hk30 hbnd hi6 hi7 hi8
    clear hkx hky hxv hyv hsx hsy htx hty hbnd hi6 hi7 hi8 hk2 hk30
    exfalso ; scalar_tac
  case vc27.h_fail =>
    -- The `i6 + i8` addition cannot overflow: `xn·2^k < 2^30` and `2^(k−1) ≤ 2^29`.
    rename_i hx hy hxy xv hxv yv hyv kx hkx kx1 hkx1 ky hky ky1 hky1 hle sx hsx sy hsy hne
      hle2 tx htx ty hty hne2 p hp i6 hi6 i7 hi7 i8 hi8 hovf
    obtain ⟨hk2, hk30, hbnd⟩ := hp
    obtain ⟨hsum, -, -, -⟩ := lca_tail_aux hk2 hk30 hbnd hi6 hi7 hi8
    have hmax : UScalar.max UScalarTy.U32 = 2 ^ 32 - 1 := by native_decide
    exfalso ; omega


@[spec]
theorem common_direct_path.spec.proof (x : LeafNodeIndex) (y : LeafNodeIndex)
  (size : TreeSize) :
  (common_direct_path.pre x y size).holds →
  ⦃ ⌜ True ⌝ ⦄ common_direct_path x y size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  intro h_pre
  apply triple_in_hypothesis (h := h_pre)
  clear h_pre
  mvcgen [common_direct_path]
  case vc2.hQ => simp
  case vc3.hQ => simp
  case vc1.hQ =>
    intro _
    -- Keep this `unfold`: without it the goal matches `common_direct_path.spec.proof` itself
    -- and `mvcgen` discharges it circularly with the very spec we are proving.
    unfold common_direct_path
    mvcgen
    -- `size` is `TreeSize.valid`-shaped here, so `scalar_tac` diverges; go through
    -- `u32_lt_nat`/`omega` instead (see `Common.lean`).
    case vc1.hQ => simp only [decide_eq_true_eq, u32_lt_nat] at * ; omega
    case vc3.hQ => simp only [decide_eq_true_eq, u32_lt_nat] at * ; omega
    case vc5.hx => omega
    case vc6.hy => omega
    case vc7.hi => simp
    case vc8.hcp => omega


@[spec]
theorem is_node_in_tree.spec.proof (node_index : TreeNodeIndex) (size : TreeSize) :
  (is_node_in_tree.pre node_index size).holds →
  ⦃ ⌜ True ⌝ ⦄ is_node_in_tree node_index size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  intro h_pre
  apply triple_in_hypothesis (h := h_pre)
  mvcgen [is_node_in_tree, pure, pre] <;> try scalar_tac
  all_goals (intros ; mvcgen)
  all_goals scalar_tac


@[spec]
theorem LeafNodeIndex.to_tree_index.spec.proof (self : LeafNodeIndex) :
  (LeafNodeIndex.to_tree_index.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄
  LeafNodeIndex.to_tree_index self
  ⦃ ⇓ res => ⌜ (LeafNodeIndex.to_tree_index.post self res).holds ⌝ ⦄
  := by
  -- `res = self·2`, hence even, and `< MAX_TREE_SIZE − 1` since the pre gives `self < MAX_INDEX`.
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [LeafNodeIndex.to_tree_index, LeafNodeIndex.to_tree_index.post]
  all_goals scalar_tac

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
  ⦃ ⌜ True ⌝ ⦄
  ParentNodeIndex.to_tree_index self
  ⦃ ⇓ res => ⌜ (ParentNodeIndex.to_tree_index.post self res).holds ⌝ ⦄
  := by
  -- `res = self·2 + 1`, hence odd, and `< MAX_TREE_SIZE − 2` since the pre gives
  -- `self < MAX_INDEX − 1`.
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [ParentNodeIndex.to_tree_index, ParentNodeIndex.to_tree_index.post]
  all_goals scalar_tac

@[spec]
theorem ParentNodeIndex.from_tree_index.spec.proof (node_index : Std.U32) :
  (ParentNodeIndex.from_tree_index.pre node_index).holds →
  ⦃ ⌜ True ⌝ ⦄ ParentNodeIndex.from_tree_index node_index ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by hax_mvcgen <;> scalar_tac

@[spec]
theorem TreeNodeIndex.new.spec.proof (index : Std.U32) :
  ⦃ ⌜ True ⌝ ⦄
  TreeNodeIndex.new index
  ⦃ ⇓ res => ⌜ (TreeNodeIndex.new.post index res).holds ⌝ ⦄
  := by
  -- Unconditional (no pre): either `index > MAX_TREE_INDEX` and the post is vacuously `true`, or
  -- `index ≤ 2^30 − 2` and the constructed index is valid — even `index ↦ Leaf (index/2)` with
  -- `index/2 ≤ 2^29 − 1 = MAX_LEAF`; odd `index ≤ 2^30 − 3 ↦ Parent ((index−1)/2)` with
  -- `(index−1)/2 ≤ 2^29 − 2 = MAX_PARENT`.  Both are tight at the boundary.
  hax_mvcgen [TreeNodeIndex.new, TreeNodeIndex.new.post, TreeNodeIndex.valid,
    LeafNodeIndex.from_tree_index, ParentNodeIndex.from_tree_index,
    LeafNodeIndex.valid, ParentNodeIndex.valid]
  all_goals scalar_tac

@[spec]
theorem TreeNodeIndex.u32.spec.proof (self : TreeNodeIndex) :
  (TreeNodeIndex.u32.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄
  TreeNodeIndex.u32 self
  ⦃ ⇓ res => ⌜ (TreeNodeIndex.u32.post self res).holds ⌝ ⦄
  := by
  -- Case split on the constructor: `Leaf l ↦ 2l` with `l < 2^29`, `Parent p ↦ 2p+1` with
  -- `p < 2^29 − 1`; both are `< MAX_TREE_SIZE − 1`.
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [TreeNodeIndex.u32, TreeNodeIndex.u32.pre, TreeNodeIndex.u32.post]
  -- NOTE (post-registration): the VCs now keep `self` abstract, so both the value hypothesis
  -- (`↑r = match self with …`) and the validity hypothesis (`b = match self with …`) are stuck
  -- behind an un-reduced `match`.  Split the constructor first, then `simp_all` reduces both
  -- matches to plain linear facts that `scalar_tac` can use.
  all_goals cases self
  all_goals simp_all
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
  -- Discharge every purely-integer VC first; what survives is exactly the `Nat.log`/shift residue.
  -- `scalar_tac` is safe in *this* declaration (no symbolic `2 ^ e` survives `simp_all!` here) and
  -- now benefits from the `@[scalar_tac Nat.log 2 x]`/`@[scalar_tac 1 <<< k % U32.size]` extensions.
  all_goals try scalar_tac
  -- NB: blanket closers abort with `maximum recursion depth` (uncatchable by `try`), so they are
  -- NOT used here; the single remaining leaf gets an explicit `rename_i …` script instead.
  -- Exactly ONE VC survives: `vc1.h_ok`, i.e. `valid (1 <<< (log₂ nodes + 1) − 1)`.  Note the
  -- extracted body uses a *shift*, not `u32::pow`, so the leaf is `1 <<< e % U32.size` shaped.
  case vc1.h_ok =>
    rename_i r3 r2 r1 r hnodes hL hr2 hr1 hrv hge1
    -- `nodes < 2^30` gives `log₂ nodes ≤ log₂ (2^30 − 1) = 29`, hence the shift `e = L + 1 ≤ 30`
    -- does not wrap and `1 <<< e % U32.size = 2^e`.
    have hpow30 : (2 : Nat) ^ (29 + 1) - 1 = 1073741823 := by norm_num
    have hle : (↑nodes : Nat) ≤ 2 ^ (29 + 1) - 1 := by omega
    have hm := Nat.log_mono_right (b := 2) hle
    rw [log2_two_pow_sub_one 29] at hm
    rw [one_shiftLeft_mod_eq (Nat.log 2 (↑nodes : Nat) + 1) (by omega),
      log2_two_pow_sub_one]
    -- Remaining: `2 ≤ 2^(L+1) ≤ 2^30`, both from `L ≤ 29`.
    have hge : 2 ≤ (2 : Nat) ^ (Nat.log 2 (↑nodes : Nat) + 1) := by
      rw [pow_succ]
      have h1 : 1 ≤ (2 : Nat) ^ Nat.log 2 (↑nodes : Nat) := Nat.one_le_two_pow
      omega
    have hb : (2 : Nat) ^ (Nat.log 2 (↑nodes : Nat) + 1) ≤ 2 ^ 30 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h30 : (2 : Nat) ^ 30 = 1073741824 := by norm_num
    exact ⟨by omega, by omega, rfl⟩

@[spec]
theorem TreeSize.leaf_count.spec.proof (self : TreeSize) :
  ⦃ ⌜ True ⌝ ⦄
  TreeSize.leaf_count self
  ⦃ ⇓ res => ⌜ (TreeSize.leaf_count.post self res).holds ⌝ ⦄
  := by
  -- Unconditional: `res = self/2 + 1` is immediate; the `≤ MAX_LEAF_COUNT` conjunct is guarded by
  -- `TreeSize.valid self`, which forces `self = 2^(log2 self + 1) − 1 ≤ 2^30` — an odd value, hence
  -- `≤ 2^30 − 1`, hence `self/2 + 1 ≤ 2^29 = MAX_LEAF_COUNT`.
  -- NOTE (post-registration): with `TreeSize.valid`, `log2`, `leading_zeros` and `u32::pow` now
  -- registered as `@[spec]`/`@[step]`, mvcgen no longer *unfolds* the
  -- `leading_zeros`/`Nat.log`/`2 ^ e` chain — `valid self` arrives as one opaque hypothesis
  -- `decide (1 ≤ self ∧ self ≤ 2^30 ∧ self = 2^(log₂ self + 1) − 1) = true`.  Consequently the
  -- former `vc12.h_ok.pre` (pow bound `2 ^ e ≤ u32::MAX`), `vc19.h_fail` (`1 ≤ 2 ^ e`) and
  -- `vc21.h_fail` (`leading_zeros ≤ 31`) blocks are UNNECESSARY: those VCs are discharged by the
  -- registered specs — and so are the former `MAX_TREE_SIZE = 1 <<< 30` side conditions, which no
  -- longer show up as VCs at all.  Exactly three VCs survive: `vc1.hQ` (the `≤ MAX_LEAF_COUNT`
  -- bound), `vc2.hQ` (the two spellings of `self/2 + 1` agree) and `vc3.h_fail` (no overflow).
  -- CAUTION: the surviving `valid` hypothesis still carries a symbolic `2 ^ (Nat.log 2 self + 1)`,
  -- which `scalar_tac`'s preprocessing loops on, so it is destructed and `clear`ed first.
  hax_mvcgen [TreeSize.leaf_count, TreeSize.leaf_count.post]
  case vc1.hQ =>
    -- `self/2 + 1 ≤ MAX_LEAF_COUNT = 2^29`: `self = 2^(log₂ self + 1) − 1` is odd and `≤ 2^30`,
    -- hence `≤ 2^30 − 1`, hence `self/2 + 1 ≤ 2^29`.
    -- The context here is `res`/`q`/`s` (the two spellings of `self/2 + 1`) plus the single opaque
    -- `valid` hypothesis; the `1 <<< 30` chain no longer appears (registered specs consumed it).
    rename_i res hres q hq s hs heq hvalid
    simp only [decide_eq_true_eq] at hvalid ⊢
    obtain ⟨h1, h2, h3⟩ := hvalid
    -- `2 ^ Nat.log 2 self` is an opaque atom for `omega`; `pow_succ` exposes the `* 2`, which is
    -- what makes `self` provably odd and therefore `≠ 2^30`.
    have hp : 1 ≤ (2 : Nat) ^ Nat.log 2 (↑self : Nat) := Nat.one_le_two_pow
    rw [pow_succ] at h3
    have h30 : (2 : Nat) ^ 30 = 1073741824 := by norm_num
    have hodd : (↑self : Nat) % 2 = 1 := by omega
    have hself : (↑self : Nat) ≤ 1073741823 := by omega
    -- Drop every symbolic-power hypothesis before `scalar_tac` (its preprocessing loops on them).
    clear h2 h3 hp h30
    scalar_tac
  case vc2.hQ =>
    -- The two spellings of `self/2 + 1` (`res` from the post, `s = q + 1` from the body) agree,
    -- so this branch is unreachable.  No `valid` hypothesis here, so `scalar_tac` is pow-free.
    rename_i res hres q hq s hs hne
    exact absurd (UScalar.eq_of_val_eq (by scalar_tac)) hne
  -- `vc3.h_fail` (`self/2 + 1` cannot overflow) is pow-free, so the blanket closer is safe.
  all_goals scalar_tac

@[spec]
theorem TreeSize.inc.spec.proof (self : TreeSize) :
  (TreeSize.inc.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄
  TreeSize.inc self
  ⦃ ⇓ res => ⌜ (TreeSize.inc.post self res).holds ⌝ ⦄
  := by
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  -- `self = 2^(k+1) − 1` and `self < 2^29`, so `res = 2·self + 1 = 2^(k+2) − 1` is again `valid`.
  -- CAUTION: `TreeSize.valid` (twice: pre on `self`, post on `res`) drags in `Nat.log` and a
  -- symbolic `2 ^ e`; `scalar_tac`'s preprocessing blows the recursion limit on the latter, so the
  -- `2 ^ e ≤ u32::MAX` side condition is discharged by hand and `omega` runs first everywhere else.
  hax_mvcgen [inc, TreeSize.inc.pre, TreeSize.inc.post]
  -- NOTE (post-registration): the former `vc11.h_ok.pre` block (hand-discharged `u32::pow` side
  -- condition `2 ^ (log₂ self + 1) ≤ u32::MAX`) is UNNECESSARY — the registered `u32::pow` /
  -- `log2` / `TreeSize.valid` `@[spec]`s discharge it, and `valid` now arrives as one opaque
  -- `decide (1 ≤ self ∧ self ≤ 2^30 ∧ self = 2^(log₂ self + 1) − 1) = true` hypothesis.
  -- CAUTION: `scalar_tac` and `simp … at *` must NOT be used as blanket closers here — with a
  -- symbolic `2 ^ (Nat.log 2 ↑x + 1)` hypothesis in context they abort elaboration with
  -- `maximum recursion depth`, which neither `first` nor `try` catches.  Every `scalar_tac` below
  -- therefore runs only after the `valid` hypotheses have been destructed and `clear`ed.
  -- The residue is exactly SIX VCs: `vc1.hQ` (the two spellings of `2·self+1` agree),
  -- `vc4.hQ` (fullness of `2·self+1` — the real content), and two copies each of
  -- `vc2.h_fail` (`self*2 + 1` cannot overflow) and `vc3.h_fail` (`self*2` cannot overflow).
  case vc1.hQ =>
    rename_i hv1 rh hrh hlt r3 hr3 r2 hr2 hvr2 r1 hr1 r hr
    clear hv1 hvr2
    simp only [decide_eq_true_eq]
    apply UScalar.eq_of_val_eq
    rw [hr2, hr3, hr, hr1]
  case vc2.h_fail =>
    -- `self < 2^29`, so `self*2 + 1 < 2^30 ≤ u32::MAX`.
    exfalso
    rename_i hv1 rh hrh hlt r2 hr2 r1 hr1 hvr1 r hr hof
    clear hv1 hvr1
    have hlt' := of_decide_eq_true hlt
    scalar_tac
  case vc3.h_fail =>
    -- `self < 2^29`, so `self*2 < 2^30 ≤ u32::MAX`.
    exfalso
    rename_i hv1 rh hrh hlt r1 hr1 r hr hvr hof
    clear hv1 hvr
    have hlt' := of_decide_eq_true hlt
    scalar_tac
  case vc4.hQ =>
    -- The real content: `valid (2·self + 1)`.  `self = 2^(L+1) − 1` and `self < 2^29` give
    -- `2·self + 1 = 2^(L+2) − 1` with `L + 2 ≤ 30`, and `log₂ (2^(L+2) − 1) = L + 1`
    -- (`log2_two_pow_sub_one`), so the failure hypothesis is absurd.
    exfalso
    rename_i hv1 rh hrh hlt r1 hr1 r hr hvr
    have h2u : ((2#u32 : Std.U32) : Nat) = 2 := by rfl
    have h1u : ((1#u32 : Std.U32) : Nat) = 1 := by rfl
    have hs29 : (↑self : Nat) < 536870912 := by
      clear hv1 hvr
      have hlt' := of_decide_eq_true hlt
      scalar_tac
    apply hvr
    simp only [decide_eq_true_eq] at hv1 ⊢
    obtain ⟨k1, k2, k3⟩ := hv1
    set L := Nat.log 2 (↑self : Nat) with hLdef
    have hp1 : 1 ≤ (2 : Nat) ^ (L + 1) := Nat.one_le_two_pow
    have hpow : (2 : Nat) ^ (L + 2) = 2 ^ (L + 1) * 2 := by ring
    have hrval : (↑r : Nat) = 2 ^ (L + 2) - 1 := by
      rw [hr, hr1, h2u, h1u, hpow]; omega
    have hlog : Nat.log 2 (↑r : Nat) = L + 1 := by
      rw [hrval]; exact log2_two_pow_sub_one (L + 1)
    -- `2^(L+1) − 1 = self < 2^29` forces `L + 1 ≤ 29`, hence `2^(L+2) ≤ 2^30`.
    have h29 : (2 : Nat) ^ 29 = 536870912 := by norm_num
    have hb : (2 : Nat) ^ (L + 1) ≤ 2 ^ 29 := by omega
    have hLle : L + 1 ≤ 29 := (Nat.pow_le_pow_iff_right (by omega)).mp hb
    have hb30 : (2 : Nat) ^ (L + 2) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by omega) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [hrval]; omega
    · rw [hrval]; omega
    · rw [hlog]; exact hrval
  case vc2.h_fail =>
    exfalso
    rename_i hv1 rh hrh hlt r hr hof
    clear hv1
    have hlt' := of_decide_eq_true hlt
    scalar_tac
  case vc3.h_fail =>
    exfalso
    rename_i hv1 rh hrh hlt hof
    clear hv1
    have hlt' := of_decide_eq_true hlt
    scalar_tac

@[spec]
theorem TreeSize.dec.spec.proof (self : TreeSize) :
  (TreeSize.dec.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄
  TreeSize.dec self
  ⦃ ⇓ res => ⌜ (TreeSize.dec.post self res).holds ⌝ ⦄
  := by
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  -- `self = 2^(k+1) − 1` with `1 < self` (so `k ≥ 1`); `divCeil self 2 − 1 = 2^k − 1 = self/2`,
  -- which is again `valid`.  Same `2 ^ e` caveat as `inc`: `scalar_tac`'s preprocessing blows the
  -- recursion limit on the symbolic-power hypotheses.
  set_option maxRecDepth 40000 in
  hax_mvcgen [dec, TreeSize.dec.pre, TreeSize.dec.post]
  -- NOTE (post-registration): exactly FOUR VCs survive (the stale comment claimed the whole
  -- residue was unprovable).  `TreeSize.valid` arrives as one opaque
  -- `decide (1 ≤ ↑x ∧ ↑x ≤ 2^30 ∧ ↑x = 2^(log₂ ↑x + 1) − 1) = true` hypothesis, both on `self`
  -- (from the pre) and on the result (from the post) — no `leading_zeros`/`u32::pow` VCs at all.
  -- CAUTION: `scalar_tac`/`simp … at *` still abort uncatchably while a symbolic `2 ^ e`
  -- hypothesis is in context, so every `scalar_tac` below runs after the pow-carrying
  -- hypotheses have been destructed and `clear`ed (the `leaf_count` recipe).
  case vc1.h =>
    -- `MIN_TREE_SIZE = 1 < self` gives `self ≥ 2`.  Pow-free once `valid` is dropped.
    rename_i hv1 hmin
    clear hv1
    have hmin' := of_decide_eq_true hmin
    unfold MIN_TREE_SIZE at hmin'
    scalar_tac
  case vc1.hQ =>
    -- The two spellings of the result agree: `divCeil self 2 − 1 = self / 2` because `self` is
    -- odd (`self = 2^(L+1) − 1 = 2^L * 2 − 1`).
    rename_i hv1 hmin ru hge1 hge2 rc hrc rd hrdv hrc1 hvd re hrev
    have h2u : ((2#u32 : Std.U32) : Nat) = 2 := by rfl
    have h1u : ((1#u32 : Std.U32) : Nat) = 1 := by rfl
    simp only [decide_eq_true_eq] at hv1 ⊢
    obtain ⟨k1, k2, k3⟩ := hv1
    have hp : 1 ≤ (2 : Nat) ^ Nat.log 2 (↑self : Nat) := Nat.one_le_two_pow
    rw [pow_succ] at k3
    have hodd : (↑self : Nat) % 2 = 1 := by omega
    -- Drop every symbolic-power hypothesis (including the post's `valid` on `rd`) before `scalar_tac`.
    clear k2 k3 hp hvd
    apply UScalar.eq_of_val_eq
    rw [hrdv, hrc, hrev, h2u, h1u]
    omega
  case vc3.hQ =>
    -- The real content: `valid (self / 2)`.  `self = 2^(L+1) − 1` with `self ≥ 2` forces `L ≥ 1`,
    -- and `divCeil self 2 − 1 = 2^L − 1 = 2^((L−1)+1) − 1`, whose `log₂` is `L − 1`
    -- (`log2_two_pow_sub_one`).  So the failure hypothesis is absurd.
    exfalso
    rename_i hv1 hmin ru hge1 hge2 rc hrc rd hrdv hrc1 hvd
    have h2u : ((2#u32 : Std.U32) : Nat) = 2 := by rfl
    have h1u : ((1#u32 : Std.U32) : Nat) = 1 := by rfl
    have hs2 : 2 ≤ (↑self : Nat) := by clear hv1 hvd; scalar_tac
    apply hvd
    simp only [decide_eq_true_eq] at hv1 ⊢
    obtain ⟨k1, k2, k3⟩ := hv1
    set L := Nat.log 2 (↑self : Nat) with hLdef
    rw [pow_succ] at k3
    have h30 : (2 : Nat) ^ 30 = 1073741824 := by norm_num
    have hpow2 : (2 : Nat) ≤ 2 ^ L := by omega
    have hL1 : 1 ≤ L := by
      rcases Nat.eq_zero_or_pos L with h | h
      · simp [h] at hpow2
      · exact h
    have hL' : L - 1 + 1 = L := by omega
    have hrdval : (↑rd : Nat) = 2 ^ L - 1 := by rw [hrdv, hrc, h2u, h1u]; omega
    have hlog : Nat.log 2 (↑rd : Nat) = L - 1 := by
      rw [hrdval]
      have h := log2_two_pow_sub_one (L - 1)
      rwa [hL'] at h
    refine ⟨?_, ?_, ?_⟩
    · rw [hrdval]; omega
    · rw [hrdval]; omega
    · rw [hlog, hL']; exact hrdval
  case vc4.h_fail =>
    -- `divCeil self 2 ≥ 1` since `self ≥ 2`, so the `− 1` cannot underflow.
    exfalso
    rename_i hv1 hmin ru hge1 hge2 rc hrc hlt
    have h2u : ((2#u32 : Std.U32) : Nat) = 2 := by rfl
    have h1u : ((1#u32 : Std.U32) : Nat) = 1 := by rfl
    have hs2 : 2 ≤ (↑self : Nat) := by clear hv1; scalar_tac
    rw [h2u] at hrc
    rw [h1u] at hlt
    omega


end binary_tree.array_representation.treemath
end openmls
