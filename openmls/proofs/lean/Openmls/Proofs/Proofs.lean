-- [openmls]: treemath panic-freedom — the per-function value specs
import Aeneas
import CoreModels
import Openmls.Extraction.Types
import Openmls.Extraction.Funs
import Openmls.Extraction.Specs
import Openmls.Proofs.Common
import Openmls.Proofs.BitMath
import Openmls.Proofs.PartialSpecs
import Openmls.Proofs.PureSpecs
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

/-- Pure-`Prop` spec for `level`: the trailing-ones characterization, with a pure hypothesis pre.
    Registered `@[spec]` (user-validated exception to the "generated specs only" rule): `level`
    occurs in the postconditions of `parent`/`left`/`right`, and re-stepping its monadic post at
    every use site is a performance blocker. -/
@[spec]
theorem level.spec_pure (index : Std.U32) (hidx : (↑index : Nat) < 2 ^ 30) :
    ⦃ ⌜ True ⌝ ⦄
    level index
    ⦃ ⇓ r => ⌜ (↑r : Nat) ≤ 30
        ∧ (↑index : Nat) % 2 ^ ((↑r : Nat) + 1) = 2 ^ (↑r : Nat) - 1 ⌝ ⦄ := by
  unfold level
  mvcgen <;> first | scalar_tac | simp_all
  all_goals exact ⟨tones_le_30 _ (by omega), tones_mod _⟩


@[spec]
theorem root.spec.proof (size : TreeSize) :
  (root.pre size).holds →
  ⦃ ⌜ True ⌝ ⦄ root size ⦃ ⇓ res => ⌜ (root.post size res).holds ⌝ ⦄
  := by
  -- `root size = TreeNodeIndex.new ((1 <<< log2 size) − 1)`, post `res.valid ∧ res.u32 < size`.
  -- QUARANTINE (`Nat.log`): `TreeSize.valid` arrives self-referentially and `scalar_tac`'s
  -- preprocessing diverges with an uncatchable `maxRecDepth` (`Openmls/Issues/ScalarTacNatLogLoop.lean`);
  -- the `of_decide_eq_true` + `set`/`clear_value` preamble makes `Nat.log 2 size` opaque first.
  unfold root.pre root.post
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [root]
  all_goals
    (obtain ⟨hs1, hs2, hs3⟩ :=
        of_decide_eq_true
          (show decide (1 ≤ (↑size : Nat) ∧ (↑size : Nat) ≤ 2 ^ 30 - 1 ∧
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
  ⦃ ⌜ True ⌝ ⦄ left index ⦃ ⇓ res => ⌜ (left.post index res).holds ⌝ ⦄
  := by
  unfold left.pre left.post
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [left]
  all_goals try scalar_tac
  all_goals try (solve | simp_all | (simp_all; scalar_tac))
  -- The four value VCs (`x.u32 < index.to_tree_index` + the `TreeNodeIndex.new` validity checks,
  -- once per constructor branch); all follow from `left_bits_lt`.  NAMING: `case tag n₁ … nₙ` names
  -- the LAST `n` hypotheses, so each list must cover the goal's FULL binder count (`gᵢ` = padding).
  case vc1.hQ b0 hb0 hb0t x0 hx0 xv hxv kv hkv uv hkposv jv hjv hjv1 r1v hr1v
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 =>
    have hlt := left_bits_lt xv r1v kv jv hkv.1 (by scalar_tac) hkv.2 hjv hr1v
    scalar_tac
  case vc4.hQ b0 hb0 hb0t x0 hx0 xv hxv kv hkv uv hkposv jv hjv hjv1 r1v hr1v
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 =>
    have hlt := left_bits_lt xv r1v kv jv hkv.1 (by scalar_tac) hkv.2 hjv hr1v
    scalar_tac
  -- `TreeNodeIndex.new`'s odd branch (result `2·((idx−1)/2) + 1`).
  case vc1.hQ b0 hb0 hb0t x0 hx0 xv hxv kv hkv uv hkposv jv hjv hjv1 r1v hr1v
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 =>
    have hlt := left_bits_lt xv r1v kv jv hkv.1 (by scalar_tac) hkv.2 hjv hr1v
    scalar_tac
  case vc4.hQ b0 hb0 hb0t x0 hx0 xv hxv kv hkv uv hkposv jv hjv hjv1 r1v hr1v
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 =>
    have hlt := left_bits_lt xv r1v kv jv hkv.1 (by scalar_tac) hkv.2 hjv hr1v
    scalar_tac

@[spec]
theorem right.spec.proof (index : ParentNodeIndex) :
  (right.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄ right index ⦃ ⇓ res => ⌜ (right.post index res).holds ⌝ ⦄
  := by
  -- Mirror of `left.spec.proof`; the mask `3 <<< (k−1)` makes the result RISE by `2^(k−1)`.
  unfold right.pre right.post
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [right]
  all_goals try scalar_tac
  all_goals try (solve | simp_all | (simp_all; scalar_tac))
  -- The four value VCs, same order/shape as `left`'s.  Here BOTH conclusions of `right_bits` are
  -- needed: the `>` clause of the post and the `MAX_TREE_INDEX` range check.
  case vc1.hQ b0 hb0 hb0t x0 hx0 xv hxv kv hkv uv hkposv jv hjv hjv1 r1v hr1v
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 =>
    obtain ⟨hgt, hle⟩ :=
      right_bits xv r1v kv jv hkv.1 (by scalar_tac) hkv.2 hjv hr1v (by scalar_tac)
    scalar_tac
  case vc4.hQ b0 hb0 hb0t x0 hx0 xv hxv kv hkv uv hkposv jv hjv hjv1 r1v hr1v
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 =>
    obtain ⟨hgt, hle⟩ :=
      right_bits xv r1v kv jv hkv.1 (by scalar_tac) hkv.2 hjv hr1v (by scalar_tac)
    scalar_tac
  case vc1.hQ b0 hb0 hb0t x0 hx0 xv hxv kv hkv uv hkposv jv hjv hjv1 r1v hr1v
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 g20 g21 =>
    obtain ⟨hgt, hle⟩ :=
      right_bits xv r1v kv jv hkv.1 (by scalar_tac) hkv.2 hjv hr1v (by scalar_tac)
    scalar_tac
  case vc4.hQ b0 hb0 hb0t x0 hx0 xv hxv kv hkv uv hkposv jv hjv hjv1 r1v hr1v
      g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 =>
    obtain ⟨hgt, hle⟩ :=
      right_bits xv r1v kv jv hkv.1 (by scalar_tac) hkv.2 hjv hr1v (by scalar_tac)
    scalar_tac

/-- Value-carrying spec for `parent` (user-validated exception, mirrors `level.spec_pure`): with `v`
    the tree index of `x` and `tones v` its trailing-ones count, the parent's tree index is the
    classic bit formula.  Deliberately NOT `@[spec]`-registered: swapping it in for
    `parent.spec.proof` was measured and reverted (see `HANDOFF.md`). -/
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
  -- `x` must be split BEFORE `mvcgen`: the dependent pure pre `hx` is a `match` on `x` and the
  -- matcher splitter cannot lift it.  Safe here only because no folded monadic post is in scope yet.
  cases x
  all_goals dsimp only at hx ⊢
  all_goals hax_mvcgen [parent]
  all_goals try scalar_tac
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
  -- The value equation itself: `trailing_unique` pins `k = tones ↑v`, `parent_bits_val` supplies
  -- the right-hand side, and `from_tree_index` returns `(X − 1)/2` with `X` odd.
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
  unfold parent.pre parent.post
  intro h_pre
  apply triple_in_hypothesis (h := h_pre)
  clear h_pre
  hax_mvcgen [parent]
  all_goals try scalar_tac
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
  -- Level successor (post clause 2): `tones t2 = k+1` by `tones_parent`, and `trailing_unique` pins
  -- both `level` results, so `lvl2 = k+1 = lvl1+1`.
  case vc3.hQ =>
    rename_i v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1 xm1 hxm1 hX1
      dd hd bb hbb hbbt t2 ht2 lvl2 hlvl2 t1 ht1 lvl1 hlvl1 succ hsucc
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e1' : (↑(1#usize) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1
    rw [e2] at hd hv
    rw [e1'] at hsucc
    have hoddX : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by rw [hm1, e1, e2] at hm; omega
    have ht2v : (↑t2 : Nat) = (↑((v ||| r1) ^^^ rr) : Nat) := by omega
    have htn : tones (↑t2 : Nat) = (↑k : Nat) + 1 := by rw [ht2v, hval]; exact tones_parent _ _
    have hlvl2eq : (↑lvl2 : Nat) = (↑k : Nat) + 1 := by
      have := trailing_unique (↑t2 : Nat) (↑lvl2 : Nat) (tones (↑t2 : Nat)) hlvl2.2 (tones_mod _)
      omega
    have ht1v : (↑t1 : Nat) = (↑v : Nat) := by omega
    rw [ht1v] at hlvl1
    have hlvl1eq : (↑lvl1 : Nat) = (↑k : Nat) :=
      trailing_unique (↑v : Nat) (↑lvl1 : Nat) (↑k : Nat) hlvl1.2 hk.2
    exact decide_eq_true (UScalar.eq_of_val_eq (by omega))
  -- Validity of the result (post clause 1, `dd = (X−1)/2 ≤ 2^29−2`), by contradiction.  For a
  -- `Leaf`, `v = 2·l` is even so `tones v = 0` and the parent value collapses to `4·(v/4) + 1`.
  case vc7.hQ =>
    rename_i bb0 hbb0 hbb0t xu hxu hxune l hx v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr
      u1 hposX m hm u2 hm1 xm1 hxm1 hX1 dd hd bb hbb hbbt
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    simp only [hx] at hbb0
    rw [hbb0] at hbb0t
    have hl : (↑l : Nat) ≤ 2 ^ 29 - 1 := of_decide_eq_true hbb0t
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1
    rw [e2] at hd hv
    have hk0 : (↑k : Nat) = 0 :=
      (trailing_unique (↑v : Nat) 0 (↑k : Nat)
        (by simpa using (by omega : (↑v : Nat) % 2 = 0)) hk.2).symm
    have hXv : (↑((v ||| r1) ^^^ rr) : Nat) = 4 * ((↑v : Nat) / 4) + 1 := by
      rw [hval, hk0]; norm_num
    exact absurd (hbb.trans (decide_eq_true (by omega))) hbbt
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
  -- Same level-successor argument; the `Parent` shape adds the `2·p+1` step for `x.u32`.
  case vc3.hQ =>
    rename_i v0 hv0 v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr u1 hposX m hm u2 hm1 xm1 hxm1 hX1
      dd hd bb hbb hbbt t2 ht2 lvl2 hlvl2 t1 ht1 lvl1 hlvl1 succ hsucc
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e1' : (↑(1#usize) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1 hv
    rw [e2] at hd hv0
    rw [e1'] at hsucc
    have hoddX : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by rw [hm1, e1, e2] at hm; omega
    have ht2v : (↑t2 : Nat) = (↑((v ||| r1) ^^^ rr) : Nat) := by omega
    have htn : tones (↑t2 : Nat) = (↑k : Nat) + 1 := by rw [ht2v, hval]; exact tones_parent _ _
    have hlvl2eq : (↑lvl2 : Nat) = (↑k : Nat) + 1 := by
      have := trailing_unique (↑t2 : Nat) (↑lvl2 : Nat) (tones (↑t2 : Nat)) hlvl2.2 (tones_mod _)
      omega
    have ht1v : (↑t1 : Nat) = (↑v : Nat) := by omega
    rw [ht1v] at hlvl1
    have hlvl1eq : (↑lvl1 : Nat) = (↑k : Nat) :=
      trailing_unique (↑v : Nat) (↑lvl1 : Nat) (↑k : Nat) hlvl1.2 hk.2
    exact decide_eq_true (UScalar.eq_of_val_eq (by omega))
  -- Validity for a `Parent`: `parent_val_lt_two_pow_30` gives `X < 2^30`, and `dd = 2^29−1` would
  -- force `x.u32 = MAX_ROOT_INDEX`, which the precondition excludes.
  case vc7.hQ =>
    rename_i bb0 hbb0 hbb0t xu hxu hxune p hx v0 hv0 v hv k hk k1 hk1 r2 hr2 r1 hr1 rr hrr
      u1 hposX m hm u2 hm1 xm1 hxm1 hX1 dd hd bb hbb hbbt
    have e1 : (↑(1#u32) : Nat) = 1 := by simp
    have e2 : (↑(2#u32) : Nat) = 2 := by simp
    have hb2 : (↑(536870911#u32) : Nat) = 536870911 := by simp
    simp only [hx] at hbb0 hxu
    rw [hbb0] at hbb0t
    have hp : (↑p : Nat) ≤ 2 ^ 29 - 2 := of_decide_eq_true hbb0t
    have hxune' : ¬ (xu = 536870911#u32) := by simpa using hxune
    have hval := parent_bits_val v r1 r2 rr k k1 hk.1 hk.2 hk1 hr2 hr1 hrr
    rw [e1] at hxm1 hX1 hv
    rw [e2] at hd hv0
    have hoddX : (↑((v ||| r1) ^^^ rr) : Nat) % 2 = 1 := by rw [hm1, e1, e2] at hm; omega
    have hvlt : (↑v : Nat) < 2 ^ 30 - 1 := by omega
    have hXlt := parent_val_lt_two_pow_30 (↑v : Nat) (↑k : Nat) hvlt hk.2
    rw [← hval] at hXlt
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
      exact hxune' (UScalar.eq_of_val_eq (by rw [hb2]; omega))
    exact absurd (hbb.trans (decide_eq_true (by omega))) hbbt

@[spec]
theorem sibling.spec.proof
  (index : TreeNodeIndex) :
  (sibling.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄
  sibling index
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  -- Post is `True`: pure panic-freedom, discharged from `parent.post`'s clause 1 (`p.valid`), which
  -- is exactly what `left.pre`/`right.pre` and the `level` side conditions need.  CAUTION: the
  -- `cases index <;> simp_all` fallback must stay behind `first | scalar_tac | …` — run into a
  -- folded `parent.post` hypothesis it blows the heartbeat budget on `whnf`.
  unfold sibling.pre
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [sibling]
  all_goals first | scalar_tac | (cases index <;> simp_all <;> scalar_tac)

/-! #### `sibling.pre` discharge lemmas (consumed by `copath.spec.proof`) -/

theorem max_leaf_eq : MAX_LEAF = ok 536870911#u32 := by
  unfold MAX_LEAF MAX_TREE_INDEX MAX_TREE_SIZE; rfl

theorem max_root_index_eq : MAX_ROOT_INDEX = ok 536870911#u32 := by
  unfold MAX_ROOT_INDEX MAX_TREE_SIZE; rfl

theorem sibling_pre_leaf (l : LeafNodeIndex) (hl : (↑l : Nat) ≤ 2 ^ 29 - 1) :
    (sibling.pre (TreeNodeIndex.Leaf l)).holds := by
  unfold sibling.pre TreeNodeIndex.valid LeafNodeIndex.valid TreeNodeIndex.u32
  obtain ⟨w, hw, hwv⟩ := mul2_ok l (by omega)
  simp only [max_leaf_eq, max_root_index_eq, bind_tc_ok, hw]
  have hle : (↑l : Nat) ≤ 536870911 := by omega
  have hne : (w != 536870911#u32) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro hc
    rw [hc, show ((536870911#u32 : Std.U32) : Nat) = 536870911 from rfl] at hwv
    omega
  simp [hle, hne]; mvcgen

/-- `ParentNodeIndex.to_tree_index p = 2·p + 1` as an ok-equation (no overflow below `2^32`). -/
theorem ptti_ok (p : ParentNodeIndex) (hp : 2 * (↑p : Nat) + 1 < 2 ^ 32) :
    ∃ x : Std.U32, ParentNodeIndex.to_tree_index p = ok x ∧ (↑x : Nat) = 2 * (↑p : Nat) + 1 := by
  unfold ParentNodeIndex.to_tree_index
  obtain ⟨w, hw, hwv⟩ := mul2_ok p (by
    have hsz : (2 : Nat) ^ 31 ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by omega); omega)
  unfold LeafNodeIndex.to_tree_index at hw
  rw [hw]; simp only [bind_tc_ok]
  have hadd := Aeneas.Std.UScalar.add_equiv w 1#u32
  cases hac : (w + 1#u32) with
  | ok x =>
    rw [hac] at hadd; obtain ⟨-, hxv, -⟩ := hadd
    exact ⟨x, rfl, by rw [hxv, show (↑(1#u32) : Nat) = 1 from rfl, hwv]⟩
  | fail e =>
    exfalso; rw [hac] at hadd; simp only [Aeneas.Std.UScalar.inBounds] at hadd
    rw [show (↑(1#u32) : Nat) = 1 from rfl, hwv] at hadd
    scalar_tac
  | div => rw [hac] at hadd; exact absurd hadd (by simp)

theorem max_parent_eq : MAX_PARENT = ok 536870910#u32 := by
  unfold MAX_PARENT MAX_LEAF MAX_TREE_INDEX MAX_TREE_SIZE; rfl

theorem sibling_pre_parent (p : ParentNodeIndex) (hp : (↑p : Nat) ≤ 2 ^ 29 - 2)
    (hnr : 2 * (↑p : Nat) + 1 ≠ 2 ^ 29 - 1) :
    (sibling.pre (TreeNodeIndex.Parent p)).holds := by
  unfold sibling.pre TreeNodeIndex.valid ParentNodeIndex.valid TreeNodeIndex.u32
  obtain ⟨x, hx, hxv⟩ := ptti_ok p (by omega)
  simp only [max_parent_eq, max_root_index_eq, bind_tc_ok, hx]
  have hle : (↑p : Nat) ≤ 536870910 := by omega
  have hne : (x != 536870911#u32) = true := by
    simp only [bne_iff_ne, ne_eq]
    intro hc
    rw [hc, show ((536870911#u32 : Std.U32) : Nat) = 536870911 from rfl] at hxv
    omega
  simp [hle, hne]; mvcgen

/-! ### `direct_path`: the on-path walk -/

/-- Loop invariant for `direct_path_loop` on the state `(d, x)`, with `s = ↑size = 2^(L+1) − 1`:
    `↑x < s` (inside the tree), `tones ↑x ≤ L` (on the direct path), `vecLen d = tones ↑x` (which
    yields the postcondition's `len ≤ 30`), and every collected parent `valid` and inside the tree.
    The final POSITIONAL clause pins the entry at index `i` to the level-`(i+1)` ancestor
    (`tones` of its tree index `2·e+1` is exactly `i+1`), which is what lets `direct_path.spec_pure`
    read off the path level-by-level.  The measure is `L − tones ↑x`. -/
def direct_path_loop_inv (s L : Nat)
    (p : alloc.vec.Vec ParentNodeIndex × Std.U32) : Prop :=
  (↑p.2 : Nat) < s ∧ tones (↑p.2 : Nat) ≤ L
  ∧ vecLen p.1 = tones (↑p.2 : Nat)
  ∧ (∀ e ∈ p.1.1, (↑e : Nat) ≤ 2 ^ 29 - 2 ∧ 2 * (↑e : Nat) + 1 < s)
  ∧ ∀ i (hi : i < p.1.1.length), tones (2 * (↑p.1.1[i] : Nat) + 1) = i + 1

/-- The `direct_path` walk: from an on-path node `x` inside the tree, repeatedly replace `x` by its
    parent until the root value `↑r = 2^L − 1` is reached, collecting the parents.  On exit the
    vector has length exactly `L` (`≤ 29`) and every entry is `valid` and inside the tree — the two
    per-entry clauses of `direct_path.post`, in membership form.

    ERASURE RECIPE: the step runs on `parent.spec_value`, which fires past the globally registered
    `parent.spec.proof` only via `mvcgen`'s simp-style scoped erasure `- parent.spec.proof`
    (neither a plain list entry nor a section-local `@[spec]` overrides it). -/
@[spec]
theorem direct_path_loop_spec (s L : Nat) (r : Std.U32)
    (d : alloc.vec.Vec ParentNodeIndex) (x : Std.U32)
    (hs : s = 2 ^ (L + 1) - 1) (hL : L ≤ 29) (hr : (↑r : Nat) = 2 ^ L - 1)
    (hinv : direct_path_loop_inv s L (d, x)) :
    ⦃ ⌜ True ⌝ ⦄
    direct_path_loop r d x
    ⦃ ⇓ res => ⌜ vecLen res = L
        ∧ (∀ e ∈ res.1, (↑e : Nat) ≤ 2 ^ 29 - 2 ∧ 2 * (↑e : Nat) + 1 < s)
        ∧ ∀ i (hi : i < res.1.length), tones (2 * (↑res.1[i] : Nat) + 1) = i + 1 ⌝ ⦄ := by
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
        ∧ (∀ e ∈ res.1, (↑e : Nat) ≤ 2 ^ 29 - 2 ∧ 2 * (↑e : Nat) + 1 < s)
        ∧ ∀ i (hi : i < res.1.length), tones (2 * (↑res.1[i] : Nat) + 1) = i + 1)
  · exact hinv
  · rintro ⟨dd, xx⟩ hI
    obtain ⟨hxs, hxt, hlen, hents, hpos⟩ := hI
    simp only at hxs hxt hlen hents hpos ⊢
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
        -- The pushed entry's tree index is the parent of `↑xx`, so its `tones` is one higher.
        have htp : tones (2 * (↑p : Nat) + 1) = tones (↑xx : Nat) + 1 := by
          rw [← hx1]; exact htn
        refine ⟨?_, by omega⟩
        simp only [direct_path_loop_inv]
        refine ⟨hx1s, by omega, ?_, ?_, ?_⟩
        · rw [hlen1, hlen, htn]
        · rw [hlist]
          intro e he
          rcases List.mem_append.1 he with h | h
          · exact hents e h
          · simp only [List.mem_singleton] at h
            subst h
            exact ⟨hple, by omega⟩
        · rw [hlist]
          intro i hi
          rcases Nat.lt_or_ge i dd.1.length with h | h
          · rw [List.getElem_append_left h]; exact hpos i h
          · have hie : i = dd.1.length := by
              simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega
            rw [List.getElem_concat_length hie, htp]
            have hll : dd.1.length = tones (↑xx : Nat) := hlen
            omega
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
        have htp : tones (2 * (↑p : Nat) + 1) = tones (↑xx : Nat) + 1 := by
          rw [← hx1]; exact htn
        refine ⟨?_, by omega⟩
        simp only [direct_path_loop_inv]
        refine ⟨hx1s, by omega, ?_, ?_, ?_⟩
        · rw [hlen1, hlen, htn]
        · rw [hlist]
          intro e he
          rcases List.mem_append.1 he with h | h
          · exact hents e h
          · simp only [List.mem_singleton] at h
            subst h
            exact ⟨hple, by omega⟩
        · rw [hlist]
          intro i hi
          rcases Nat.lt_or_ge i dd.1.length with h | h
          · rw [List.getElem_append_left h]; exact hpos i h
          · have hie : i = dd.1.length := by
              simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega
            rw [List.getElem_concat_length hie, htp]
            have hll : dd.1.length = tones (↑xx : Nat) := hlen
            omega
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
      -- Residue: the `spec_value` payload bounds, the `push` capacity, the parity massertions and
      -- the `↑xx − 1` underflow guard — all linear.
      all_goals scalar_tac
    · -- `xx = r`: done, and `vecLen dd = tones ↑r = L` by `tones_pow_sub_one`.
      rename_i heq
      have hxr : (↑xx : Nat) = 2 ^ L - 1 := by
        have h : (↑xx : Nat) = (↑r : Nat) := by simpa [bne_iff_ne] using heq
        rw [h, hr]
      mvcgen
      refine ⟨?_, hents, hpos⟩
      rw [hlen, hxr, tones_pow_sub_one]

/-- Pure membership-form companion of `direct_path.spec` (statement USER-VALIDATED 2026-07-28;
    the Rust spec may later gain clause 3 phrased via `level`).
    Clause 1-2 are the Rust post in membership form: at most 29 entries, every entry `valid`
    (`≤ 2^29 − 2 = MAX_PARENT`) and below `parent_count size = ↑size / 2`. Clause 3 is a
    positional strengthening needed by `copath`: the entry at position `i` is the level-`i+1`
    ancestor (`tones (2·e+1) = i+1`), so after `pop` no remaining entry can be the root.
    Deliberately NOT `@[spec]`-registered: the official registration is `direct_path.spec.proof`;
    this companion is consumed by explicit application / scoped erasure at its call sites. -/
theorem direct_path.spec_pure (node_index : LeafNodeIndex) (size : TreeSize)
    (h : (direct_path.pre node_index size).holds) :
    ⦃ ⌜ True ⌝ ⦄
    direct_path node_index size
    ⦃ ⇓ res => ⌜ vecLen res ≤ 29
        ∧ (∀ e ∈ res.1, (↑e : Nat) ≤ 2 ^ 29 - 2 ∧ (↑e : Nat) < (↑size : Nat) / 2)
        ∧ (∀ i, (hi : i < res.1.length) → tones (2 * (↑res.1[i] : Nat) + 1) = i + 1) ⌝ ⦄ := by
  -- ERASURE RECIPE: `root.spec.proof`'s post (`res.valid ∧ res.u32 < size`) is too weak — the loop
  -- spec needs the root VALUE `↑r = 2^L − 1`.  So `root` is stepped by its body
  -- (`- root.spec.proof, root`, plus the two `from_tree_index` unfolds inside `TreeNodeIndex.new`),
  -- which is where `log2_mvcgen_spec` supplies `↑ = Nat.log 2 ↑size`.  `direct_path_loop_spec` is
  -- erased too: its `s`/`L` are explicit arguments no unifier can guess, so it is applied by hand.
  apply triple_in_hypothesis (h := h) ; clear h
  hax_mvcgen [direct_path.pre, direct_path, - root.spec.proof, root, TreeNodeIndex.new,
    LeafNodeIndex.from_tree_index, ParentNodeIndex.from_tree_index,
    - direct_path_loop_spec]
  -- Same `Nat.log`-quarantine preamble as `root.spec.proof`: make `L := Nat.log 2 ↑size` opaque
  -- (term-level `of_decide_eq_true`, then `clear_value`) BEFORE any `scalar_tac` runs.
  all_goals
    (obtain ⟨hs1, hs2, hs3⟩ :=
        of_decide_eq_true
          (show decide (1 ≤ (↑size : Nat) ∧ (↑size : Nat) ≤ 2 ^ 30 - 1 ∧
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
  -- The two surviving goals are the loop call, once per `TreeNodeIndex.new` branch: `2^L − 1` is
  -- even only for `L = 0` (the singleton tree), odd otherwise, and BOTH reconstructions collapse
  -- back to `↑rt = 2^L − 1` by `omega`.  The last EIGHT inaccessible hypotheses sit at the same
  -- depth in both branches — root value, `Vec::new`, `to_tree_index`, then the two hypotheses the
  -- `set L` above re-introduced at the very end (`hdec`/`hlog`); the `rename_i` count must cover
  -- those two as well or the names slide by two slots.
  all_goals
    (rename_i rt hrt dv hdv xv hxv hdec hlog
     have hx2 : (↑xv : Nat) = 2 * (↑node_index : Nat) := by scalar_tac
     have hxt : tones (↑xv : Nat) = 0 := tones_even _ (by omega)
     have hinv : direct_path_loop_inv (↑size : Nat) L (dv, xv) := by
       simp only [direct_path_loop_inv]
       refine ⟨by scalar_tac, by rw [hxt]; omega, ?_, ?_, ?_⟩
       · rw [hxt]; exact hdv.1
       · rw [hdv.2]; simp
       · rw [hdv.2]; simp
     mspec (direct_path_loop_spec (↑size : Nat) L rt dv xv (by omega) hL29 (by scalar_tac) hinv)
     intro hpost
     obtain ⟨hlen, hents, hpos⟩ := hpost
     refine ⟨by omega, ?_, hpos⟩
     intro e he
     obtain ⟨he1, he2⟩ := hents e he
     exact ⟨he1, by omega⟩)

@[spec]
theorem direct_path.spec.proof (node_index : LeafNodeIndex) (size : TreeSize) :
  (direct_path.pre node_index size).holds →
  ⦃ ⌜ True ⌝ ⦄
  direct_path node_index size
  ⦃ ⇓ res => ⌜ (direct_path.post node_index size res).holds ⌝ ⦄
  := by
  -- The function's behaviour comes entirely from `direct_path.spec_pure` (membership form); the
  -- Rust post is then re-derived by STEPPING THE POST do-block (`len`/`deref`/`iter`/`all`).
  -- SELF-SPEC HAZARD: this very theorem is `@[spec]`-registered, so it must be erased from the
  -- `mvcgen` set (`- direct_path.spec.proof`) or the call would be discharged by itself.
  -- The `all` step goes through the trusted `slice_iter_all_spec`, whose predicate `P` is not
  -- inferable: it arrives as the `vc1.P` goal (a `Bool` with the element in scope) and is
  -- instantiated with the pointwise value of the Rust closure `__18.ensures.closure`.
  intro h_pre
  unfold direct_path.post
  hax_mvcgen [- direct_path.spec.proof, direct_path.spec_pure]
  case vc1.P =>
    rename_i e
    exact decide ((↑e : Nat) ≤ 2 ^ 29 - 2 ∧ (↑e : Nat) < (↑size : Nat) / 2)
  case vc1.hQ =>
    rename_i h1 e1 he1 e2 he2 hlt h2 f1 hf1 f2 hf2
    clear h1 h2
    scalar_tac
  case vc2.hcall =>
    rename_i e he
    unfold __18.ensures.closure.Insts.CoreOpsFunctionFnMutTupleSharedParentNodeIndexBool.call_mut
      ParentNodeIndex.valid ParentNodeIndex.u32 TreeSize.parent_count
    rw [show binary_tree.array_representation.treemath.MAX_PARENT = ok 536870910#u32 by
      unfold MAX_PARENT MAX_LEAF MAX_TREE_INDEX MAX_TREE_SIZE; rfl]
    obtain ⟨q, hq, hqv⟩ := Aeneas.Std.UScalar.div_spec (x := size) (y := 2#u32) (by scalar_tac)
    simp [hq, hqv]
    split <;> rename_i hb <;> simp [hb]
  case vc3 =>
    rename_i hpre e1 he1 e2 he2 hlt v hlen hents hposs l hl29 hlv s hs it hit p hp
    rw [hp]
    simp only [sliceIterElems, hit, hs, List.all_eq_true, decide_eq_true_eq]
    intro e he
    exact hents e he
  case vc4 =>
    rename_i hpre e1 he1 e2 he2 hlt v hlen hents hposs l hl29 hlv
    clear hpre
    scalar_tac

@[spec]
theorem copath.spec.proof (leaf_index : LeafNodeIndex) (size : TreeSize) :
  (copath.pre leaf_index size).holds →
  ⦃ ⌜ True ⌝ ⦄ copath leaf_index size ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [copath, - copath.spec.proof, - direct_path.spec.proof, direct_path.spec_pure,
    slice_iter_map_collect_spec, into_map_collect_spec]
  case vc1.hQ =>
    rename_i h1 e1 he1 e2 he2 hlt h2 f1 hf1 f2 hf2
    clear h1 h2
    scalar_tac
  case vc4.hQ =>
    rename_i hdec e1 he1 e2 he2 hlt dp hdp b hbne hb pr hpr
    obtain ⟨hsz1, hsz, hsz3⟩ := of_decide_eq_true hdec
    clear hdec
    obtain ⟨hlen29, hents, hposs⟩ := hdp
    obtain ⟨hpr2, -⟩ := hpr
    simp only [alloc.slice.Slice.into_vec]
    mvcgen [alloc.slice.Dummy.into_vec, rust_primitives.sequence.seq_from_boxed_slice,
      alloc.vec.from_seq, slice_iter_map_collect_spec, into_map_collect_spec]
    -- mvcgen stalls at the `map`/`collect` pair: apply the trusted contract by hand.
    rename_i s hs it hit
    have hmc := slice_iter_map_collect_spec
      copath.closure.Insts.CoreOpsFunctionFnMutTupleSharedParentNodeIndexTreeNodeIndex
      it () TreeNodeIndex.Parent (by intro e he; rfl)
    obtain ⟨mv, hmv⟩ := triple_noThrow_exists_ok hmc
    have hmvp := triple_noThrow_elim hmc hmv
    simp only [SPred.down_pure] at hmvp
    rw [← Std.Do.WP.bind, ← bind_assoc, hmv]
    simp only [bind_tc_ok]
    mvcgen [vec_append_spec, into_map_collect_spec]
    · -- `Vec::append` capacity: `|[Leaf leaf_index]| + |dp.dropLast| = 1 + (|dp| − 1) ≤ Usize.max`.
      simp only [hmvp, List.length_map, sliceIterElems, hit, hs, hpr2, List.length_dropLast]
      simp only [Aeneas.Std.Array.to_slice, Aeneas.Std.Array.make, List.length_cons,
        List.length_nil, Nat.zero_add]
      have hne0 : vecLen dp ≠ 0 := by intro hh; exact hbne (by rw [hb, hh]; rfl)
      rw [vecLen_eq_length] at hne0
      have hdm : dp.val.length ≤ Std.Usize.max := dp.property
      omega
    · -- The final `into_iter` / `map sibling` / `collect`.  `mvcgen` will not re-associate the
      -- three-step do-block into the shape of `into_map_collect_spec`, so the trusted contract is
      -- applied by hand (as for `slice_iter_map_collect_spec` above), with
      --   `hsafe : ∀ e ∈ [Leaf leaf_index] ++ (dp.dropLast).map Parent, ⦃True⦄ sibling e ⦃True⦄`
      -- derived from the registered `sibling.spec.proof` by computing `(sibling.pre e).holds`.
      rename_i r hr
      have hrl : r.1.val
          = TreeNodeIndex.Leaf leaf_index :: (dp.val.dropLast).map TreeNodeIndex.Parent := by
        rw [hr.1, hmvp]
        simp only [sliceIterElems, hit, hs, hpr2, Aeneas.Std.Array.to_slice,
          Aeneas.Std.Array.make, List.cons_append, List.nil_append]
      have hsafe : ∀ e ∈ r.1.val, ⦃ ⌜ True ⌝ ⦄ sibling e ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
        intro t ht
        rw [hrl] at ht
        refine sibling.spec.proof t ?_
        rcases List.mem_cons.1 ht with rfl | hR
        · -- `Leaf leaf_index`: `↑leaf_index < ↑size/2 + 1 ≤ 2^29` and `2·leaf` is even.
          refine sibling_pre_leaf leaf_index ?_
          have hlt' : (↑e1 : Nat) < (↑e2 : Nat) := by
            simpa only [u32_lt_nat] using of_decide_eq_true hlt
          rw [he1, he2] at hlt'
          omega
        · -- `Parent p` with `p ∈ dp.dropLast`.
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hR
          refine sibling_pre_parent p (hents p (List.dropLast_subset _ hp)).1 ?_
          have hlen' : dp.val.length ≤ 29 := by
            simpa only [vecLen_eq_length] using hlen29
          exact dropLast_entries_ne_max_root dp.val hlen' hposs p hp
      have hcol := into_map_collect_spec r.1 sibling hsafe
      obtain ⟨cv, hcv⟩ := triple_noThrow_exists_ok hcol
      rw [← Std.Do.WP.bind, hcv]
      trivial

@[spec]
theorem lowest_common_ancestor.spec.proof (x : LeafNodeIndex) (y : LeafNodeIndex) :
  (lowest_common_ancestor.pre x y).holds →
  ⦃ ⌜ True ⌝ ⦄ lowest_common_ancestor x y ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  -- The pre forces two distinct valid (`< 2^29`) leaves, so `level` returns `0` and both
  -- early-return branches are unreachable; the shift-loop tail closes via `lca_tail_aux`.
  unfold lowest_common_ancestor.pre LeafNodeIndex.valid LeafNodeIndex.u32
  intro h_pre
  apply triple_in_hypothesis (h := h_pre)
  clear h_pre
  mvcgen ; simp
  case vc2.hQ =>
    grind
  case vc3.hQ =>
    grind
  simp_all; intro
  hax_mvcgen [lowest_common_ancestor]
  all_goals try scalar_tac
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
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [LeafNodeIndex.to_tree_index]
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
  ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [ParentNodeIndex.to_tree_index]
  all_goals scalar_tac

@[spec]
theorem ParentNodeIndex.from_tree_index.spec.proof (node_index : Std.U32) :
  (ParentNodeIndex.from_tree_index.pre node_index).holds →
  ⦃ ⌜ True ⌝ ⦄ ParentNodeIndex.from_tree_index node_index ⦃ ⇓ res => ⌜ True ⌝ ⦄
  := by hax_mvcgen <;> scalar_tac

@[spec]
theorem TreeNodeIndex.new.spec.proof (index : Std.U32) :
  (TreeNodeIndex.new.pre index).holds →
  ⦃ ⌜ True ⌝ ⦄
  TreeNodeIndex.new index
  ⦃ ⇓ res => ⌜ (TreeNodeIndex.new.post index res).holds ⌝ ⦄
  := by
  -- With `index ≤ 2^30 − 2` the constructed index is valid: even `index ↦ Leaf (index/2)` with
  -- `index/2 ≤ MAX_LEAF`; odd `index ↦ Parent ((index−1)/2)` with `(index−1)/2 ≤ MAX_PARENT`.
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  hax_mvcgen [TreeNodeIndex.new, TreeNodeIndex.new.pre, TreeNodeIndex.new.post,
    TreeNodeIndex.valid,
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
  -- Both hypotheses are stuck behind an un-reduced `match self`: split the constructor first, then
  -- `simp_all` reduces them to linear facts for `scalar_tac`.
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
  -- Discharge the purely-integer VCs; what survives is the `Nat.log`/shift residue.
  all_goals try scalar_tac
  -- QUARANTINE: blanket closers abort with an uncatchable `maximum recursion depth` here, so the
  -- one surviving VC (`vc1.h_ok`, `valid (1 <<< (log₂ nodes + 1) − 1)`) gets an explicit script.
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
theorem TreeSize.inc.spec.proof (self : TreeSize) :
  (TreeSize.inc.pre self).holds →
  ⦃ ⌜ True ⌝ ⦄
  TreeSize.inc self
  ⦃ ⇓ res => ⌜ (TreeSize.inc.post self res).holds ⌝ ⦄
  := by
  intro h_pre
  apply triple_in_hypothesis (h := h_pre) ; clear h_pre
  -- `self = 2^(k+1) − 1`, so `res = 2·self + 1 = 2^(k+2) − 1` is again `valid`.  QUARANTINE:
  -- `TreeSize.valid` drags in `Nat.log` / a symbolic `2 ^ e`, on which `scalar_tac` blows the
  -- recursion limit — every `scalar_tac` below runs only after those hypotheses are `clear`ed.
  hax_mvcgen [inc, TreeSize.inc.pre, TreeSize.inc.post]
  case vc1.hQ =>
    -- `_ r3 hr3 r2 hr2 _ r1 hr1 r hr`: skips the pre's `valid self` (never used here).
    rename_i _ r3 hr3 r2 hr2 _ r1 hr1 r hr
    simp only [decide_eq_true_eq]
    apply UScalar.eq_of_val_eq
    rw [hr2, hr3, hr, hr1]
  case vc2.h_fail =>
    -- `self ≤ MAX_TREE_SIZE − 1 = 2^30 − 2`, so `self*2 + 1 ≤ 2^31 − 3 < u32::MAX`.  No validity
    -- needed — the raw `inc.pre` bound already suffices.
    exfalso
    rename_i hv1 hlt _ _ _ _ hvr _ hrv hof
    clear hv1 hvr
    have hlt' := of_decide_eq_true hlt
    scalar_tac
  case vc3.h_fail =>
    -- `self ≤ 2^30 − 2`, so `self*2 ≤ 2^31 − 4 < u32::MAX`.
    exfalso
    rename_i hv1 hlt _ _ _ _ hvr hof
    clear hv1 hvr
    have hlt' := of_decide_eq_true hlt
    scalar_tac
  case vc4.hQ =>
    -- The real content: `valid (2·self + 1)`.  The new pre only gives `self < 2^30 − 1`, so the
    -- `self ≤ 2^29 − 1` bound must come from validity: `self = 2^(L+1) − 1 < 2^30 − 1` forces
    -- `2^(L+1) ≤ 2^30 − 1`, hence `L + 1 ≤ 29`.  Then `2·self + 1 = 2^(L+2) − 1 ≤ 2^30 − 1` and
    -- `log₂ (2^(L+2) − 1) = L + 1` (`log2_two_pow_sub_one`), so the failure hypothesis is absurd.
    exfalso
    rename_i hv1 hlt r1 hr1 r hr hvr
    have h2u : ((2#u32 : Std.U32) : Nat) = 2 := by rfl
    have h1u : ((1#u32 : Std.U32) : Nat) = 1 := by rfl
    -- Extract the numeric pre-bound while no symbolic `2 ^ e` is in context (`scalar_tac` hazard).
    have hltn : (↑self : Nat) < 1073741823 := by
      clear hv1 hvr
      have hlt' := of_decide_eq_true hlt
      scalar_tac
    apply hvr
    simp only [decide_eq_true_eq] at hv1 ⊢
    obtain ⟨k1, k2, k3⟩ := hv1
    set L := Nat.log 2 (↑self : Nat) with hLdef
    have hp1 : 1 ≤ (2 : Nat) ^ (L + 1) := Nat.one_le_two_pow
    have hpow : (2 : Nat) ^ (L + 2) = 2 ^ (L + 1) * 2 := by ring
    have h30 : (2 : Nat) ^ 30 = 1073741824 := by norm_num
    have hrval : (↑r : Nat) = 2 ^ (L + 2) - 1 := by
      rw [hr, hr1, h2u, h1u, hpow]; omega
    have hlog : Nat.log 2 (↑r : Nat) = L + 1 := by
      rw [hrval]; exact log2_two_pow_sub_one (L + 1)
    have hL29 : L + 1 ≤ 29 := by
      by_contra hc
      have h30le : (2 : Nat) ^ 30 ≤ 2 ^ (L + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hb30 : (2 : Nat) ^ (L + 2) ≤ 2 ^ 30 := Nat.pow_le_pow_right (by omega) (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [hrval]; omega
    · rw [hrval]; omega
    · rw [hlog]; exact hrval
  case vc2.h_fail =>
    exfalso
    rename_i hv1 hlt _ hrv hof
    clear hv1
    have hlt' := of_decide_eq_true hlt
    scalar_tac
  case vc3.h_fail =>
    exfalso
    rename_i hv1 hlt hof
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
  -- which is again `valid`.
  set_option maxRecDepth 40000 in
  hax_mvcgen [dec, TreeSize.dec.pre, TreeSize.dec.post]
  -- QUARANTINE: `scalar_tac`/`simp … at *` abort uncatchably while a symbolic `2 ^ e` hypothesis
  -- is in context — every `scalar_tac` below runs after the `valid` hypotheses are `clear`ed.
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
