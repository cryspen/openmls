# Handoff — treemath panic-freedom proofs

Files (Aeneas→Lean, under `Openmls/Proofs/`). Gate: `lake build Openmls.Proofs.Proofs`
(GREEN). Do NOT run extraction (aeneas/charon/hax); edit Lean only. Do NOT use git.
The 1840-line monolith was split into five modules (see `HANDOFF_treemath_refactor.md`):
`Common.lean` (loop driver + triple helpers + `vecLen` + `attribute [spec] uncurry`),
`BitMath.lean` (pure-Nat `tones`/`parent` bit lemmas), `MissingCoreSpecs.lean` (PROVED core specs),
`AdmittedCoreSpecs.lean` (the 11 admitted core contracts — the audit surface), and
`Proofs.lean` (per-function treemath value specs + the 9 `.spec.proof` obligations; NO `sorry`).
Import DAG: `Common ← {BitMath, MissingCoreSpecs, AdmittedCoreSpecs} ← Proofs`.
NOTE: repo was restructured into git worktrees — this work lives in
`/home/cblaudeau/openmls/main/...` (branch `proofs/extraction`); `dev/` is a separate older branch.

## ✅ ALL 9/9 spec.proof obligations PROVED
- `level`, `root`, `left`, `right`, `is_node_in_tree`, `common_direct_path`,
  `lowest_common_ancestor`, `direct_path`, **`copath`** (NEW — the last one).
- The ONLY remaining `sorry`s are 11 *trusted* `@[spec]` contracts for opaque stdlib axioms, now all
  living in `AdmittedCoreSpecs.lean` and all stated purely over `core`/`alloc` (no treemath symbols),
  REVIEW for faithfulness: `deref_mut_slice_spec`, `reverse_slice_spec`, `vec_index_spec`,
  `vec_push_spec`, `min_usize_spec`, `u32_cmp_spec`, `sharedavec_into_iter_spec`,
  `slice_iter_next_spec`, `vec_is_empty_spec`, `vec_pop_spec`, and the generic
  `into_map_collect_spec {T} (v : Vec T) (f : T → Result T)`.
  (`vec_push_spec` is strengthened to track the element list; `vec_len_spec`, `vec_new_spec`,
  `vec_with_capacity_spec` are PROVED, in `MissingCoreSpecs.lean`.)
- `into_map_collect_sibling_spec` (the `sibling` instance) is now **PROVED** (not admitted) in
  `Proofs.lean` by instantiating `into_map_collect_spec` at `sibling`; it kept its statement and
  stays `@[spec]`. `SiblingSafe` (treemath) also lives in `Proofs.lean`.

### `copath` proof structure (NEW)
- `direct_path_elems_spec` — strengthened `direct_path` post: every output node `e` has
  `2·e+1 < 2^31−1` AND `vecLen ≤ 30` (proved by strengthening `direct_path_loop_spec`'s invariant
  with an element predicate + length bound; `direct_path.spec.proof` weakens it to `True`).
- `sibling_noPanic` (node value `< 2^31−1` ⇒ `sibling` panic-free), via `parent_tni_spec`
  (factored from `parent_new_spec`), `parent_val_lt` (parent value stays `< 2^31`, no carry),
  `left_noPanic`/`right_noPanic` (the existing `left.spec`/`right.spec` need `< 2^29` which is too
  strong, so these are proved fresh via `level_tones_eq`), `tones_le_30`, `tones_pos_of_odd`,
  `ptti_ok`. `siblingSafe_leaf`/`siblingSafe_parent` lift it to the two node shapes.
- `copath_loop_spec` — the accumulation loop via `loop_spec_measure` (measure
  `(sliceIterElems iter).length`), threading a `SiblingSafe`-for-all invariant + a sum bound for
  `push`. Uses the trusted `slice_iter_next_spec`.
- `copath.spec.proof` — `mvcgen` threads all the iterator contracts; the final
  `into_iter>>=map>>=collect` tail is closed by recombining the decomposed `wp` with
  `rw [← Std.Do.WP.bind]` then extracting `into_map_collect_sibling_spec`'s ok-equation.
  GOTCHA: `mspec`/`exact` do NOT close a bare `(wp⟦block⟧ Q).down` from a whole-block Triple
  (`mspec` peels only the leading atom; `Triple = ⌜True⌝ ⊢ₛ wp`, not `wp.down`); recombine +
  `triple_noThrow_exists_ok` + `rw [okEq]; simp [WP.wp, PredTrans.apply]` instead.

## (historical) Proved (8/9 spec.proof + infrastructure)
- `level`, `root`, `left`, `right`, `is_node_in_tree`, `common_direct_path`,
  `lowest_common_ancestor`, **`direct_path`** (NEW). Only `copath` remained (now done).
- ORDERING NOTE: `common_direct_path` calls `direct_path`, so its `.spec.proof` must come
  AFTER `direct_path.spec.proof`. Both `direct_path.spec.proof` and `common_direct_path.spec.proof`
  (and `copath`, `lowest_common_ancestor`) are now at the END of the file, after all the
  helper lemmas. The early-file slots only hold a comment pointing to the end.
- Helpers: `new_spec` (round-trip), `level_char`, the pure-Nat `parent` bit lemmas
  (`parent_bitops_eq`, `parent_val_arith`, `parent_val_u32`, `tones`, `tones_mod`,
  `pow_sub_one_mod`, `trailing_unique`).
- lca helpers (end of file): `level_even` / `level_even_eq`, `even_shift_eq_ge_two`, `mul2_ok`,
  `lca_loop0_spec`, `lca_tail_aux`.
- NEW for `parent`/`direct_path` (end of file, in order):
  - `new_u32_eq` (new∘u32 round-trip as ok-pair), `level_tones_eq` (`level x = ok ⟨tones ↑x⟩`).
  - `parent_index_val` (the `parent` bit-chain U32 value = `parent_val_u32` RHS, + odd / ≥1 / <2^32).
  - `parent_new_tti_spec` (full `new>>=parent>>=to_tree_index` value) AND **`parent_new_spec`**
    (`new>>=parent` → `ParentNodeIndex` `par` with `2·par+1 = <parent index>`, `par < 2^31`).
    `direct_path` uses `parent_new_spec`, NOT the tti version (the loop body has a `Vec.push`
    between `parent` and `to_tree_index`, so the bundled tti spec doesn't fit).
  - `tones_parent` (`tones (2^(k+2)q + (2^(k+1)−1)) = k+1`), `tones_pow_sub_one` (`tones(2^d−1)=d`),
    `tones_even`, `parent_lt` (parent value stays `< 2^(d+1)`).
  - `log2_eq` / `log2_spec` (`log2 s = Nat.log 2 ↑s` via `leading_zeros`; uses `BitVec.leadingZeros`,
    `Nat.pow_log_le_self`, `Nat.lt_pow_succ_log_self`), `new_u32_triple`, `root_u32_spec`
    (`(root size).u32 = 2^(log2 size) − 1`, `log2 ≤ 30`, `size < 2^(log2+1)`).
  - `vec_new_spec` (Vec::new → empty), `direct_path_loop_spec` (the tree-walk loop, measure
    `d − tones x`, inv `tones x ≤ d ∧ x < 2^(d+1) ∧ vecLen ≤ tones x`).

### KEY techniques (NEW, from `parent_new_spec` / `direct_path`)
- **`new_spec` is global `@[spec]` and fires first.** When you want a spec for `new x >>= parent`
  (or `new x >>= parent >>= …`), `mvcgen` peels `new x` via `new_spec` BEFORE your combined spec
  can match. Fix: don't `mvcgen` over `new`; instead **extract your combined spec as an ok-equation**
  (`triple_noThrow_exists_ok`/`_elim`) and `rw [← bind_assoc, hOkEq]; simp [bind_tc_ok]` to splice
  the value in. Used in `direct_path_loop_spec` (parent step) and the `direct_path` prefix (root∘u32).
- **`← bind_assoc` to expose a prefix.** `m >>= fun a => f a >>= g` reassociates to
  `(m >>= f) >>= g`; then `rw` the ok-equation for `m >>= f`. Essential for splicing `root>>=u32`
  and `new>>=parent` ok-equations into larger do-blocks.
- **Extracting `.pre.holds` facts (direct_path):** unfold `pre` + the helper fns + `MAX_TREE_SIZE`,
  `simp [Result.holds, Triple, WP.wp, PredTrans.apply]`, `rw` the constant `<<<`/`*`/`-` to `ok`
  literals (by `rfl`), `simp [Functor.map]` (turns the `(·=true) <$>` wrapper steppable), then
  `by_contra; rw [if_neg …]; simp` per `if`. Division/`+1` in the leaf-count check: `UScalar.div_spec`
  (∃-form) + `UScalar.add_equiv` (cases) to read off the inequality.
- **Scalar op specs:** `UScalar.sub_equiv` / `add_equiv` (match-on-result, like `mul_equiv`),
  `UScalar.div_spec` (∃ z, … = ok z ∧ ↑z = ↑x/↑y), `UScalar.ShiftLeft_spec`,
  `UScalar.cast_val_eq` (`(cast t x).val = x.val % 2^t.numBits`). `Vec::new`/`with_capacity`/`len`
  proved by `unfold …; mvcgen`.
- **Closing a `(wp⟦e⟧ Q).down` goal from a spec hypothesis:** `intro h; mspec h` then `simp_all`
  (used in `root_u32_spec` for the `new>>=u32` tail). `exact triple_of_ok …` does NOT defeq-match
  the bare `.down` form.

### KEY techniques discovered proving `lowest_common_ancestor` (reuse for parent/direct_path)
- **`mvcgen` vs `hax_mvcgen` + spec override:** `hax_mvcgen` force-applies the registered
  `level.spec.proof` (whose `level.post`-`.holds` postcondition does NOT reduce → mvar crash).
  Plain **`mvcgen [helper_spec, …]`** is gentler. BUT a globally-`@[spec]` lemma still wins over
  a locally-passed one, and `@[spec]` **cannot be erased** (`attribute [-spec]` fails).
  Workaround: **eliminate the offending call before `mvcgen`** by stepping its args to concrete
  values (`obtain ⟨v,heq,hval⟩ := mul2_ok …; rw [heq]; simp only [bind_tc_ok]`) then
  `rw [level_even_eq v …]` so `level v` becomes `ok 0` — no `level` left for mvcgen to mis-spec.
- **Extracting a `.pre.holds` precondition into usable facts:** `.holds` is a `Triple`. Unfold via
  `simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp, Std.Do.PredTrans.apply]`,
  then `rw [show (1#u32 <<< 30#i32 : Result U32) = ok 1073741824#u32 from by rfl]` (NB: `Result`
  has no `DecidableEq`, so `native_decide` FAILS — use `rfl`), `simp`, repeat for `/2#u32`,
  `simp [Functor.map]` (turns `<$>` into `>>=`), then case-split the residual nested `if`
  with `by_contra; rw [if_neg]; simp` to pull out `↑x<2^29 ∧ ↑y<2^29 ∧ ↑x≠↑y`.
- After `mvcgen`, **`all_goals try scalar_tac` discharges almost everything** (bounds,
  even/odd, the early-return-branch contradictions via `x≠y`, AND the unreachable
  `loop1/2/3` branches). Only the `loop0`-tail overflow/oddness VCs survive → `lca_tail_aux`.
- `IScalar.toNat p.2` (from a shift) ≠ `p.2.toNat` (from a spec post) *syntactically* → `omega`
  treats them as distinct atoms. Bridge with `rw [show p.2.toNat = IScalar.toNat p.2 from rfl]`.
- `omega` can't reason `_ % ↑2#u32`; first `rw [show (↑(2#u32):Nat)=2 from rfl] at h`. Same for
  `↑1#u32` in subtractions. `UScalar.max`/`size` literal facts: `by native_decide` (these DO work).
- **`loop_spec_measure`** — generic `Nat`-measure loop lemma with a `mvcgen`-steppable
  (`⦃⇓ r => match r | .cont => ⌜inv ∧ decr⌝ | .done => ⌜post⌝⦄`) body obligation. Reuse for every
  remaining loop. Pattern: `unfold f_loop; apply loop_spec_measure (measure:=)(inv:=)(post:=); · <init>; · intro p hinv; obtain …; unfold f_loop.body; split <;> mvcgen [specs]`.
- Trusted Vec/stdlib `@[spec]` contracts (admitted; REVIEW): `deref_mut_slice_spec`,
  `reverse_slice_spec`, `vec_index_spec`, `min_usize_spec`, `vec_push_spec`. Proved:
  `vec_len_spec`, `vec_with_capacity_spec`, `vec_new_spec`. `vec_push_spec` is still admitted —
  provable from `seq_push` (`= if (s.val++[x]).length ≤ Usize.max then ok … else fail`) but the
  `vecLen = Slice.length v.1` vs CoreModels-`Seq` representation made it murky; left trusted.
- `attribute [spec] uncurry` (top of file) — lets `mvcgen` step tuple-destructuring do-binds.

## Remaining `sorry`s (1 of 9 + the trusted Vec contracts)
Only `copath` remains among the 9 obligations. Plus the 5 admitted trusted Vec contracts above.

`copath` (`Funs.lean:1077`, loops at `1061`/`1038`) — the hardest, needs the most new scaffolding:
```
dp ← direct_path leaf size;  b ← Vec.is_empty dp;
dp1 ← if b then dp else (Vec.pop dp).2;     -- drop the root
n ← Vec.len dp1;  fp ← Vec.with_capacity (n+1);  fp1 ← Vec.push fp (Leaf leaf);
iter ← into_iter dp1;  fp2 ← copath_loop iter fp1;   -- fp2 = [Leaf leaf] ++ map Parent dp1
ii ← into_iter fp2;  m ← map ii sibling;  collect m   -- run `sibling` on every node
```
Required:
1. Trusted `@[spec]` contracts for the iterator combinators (`alloc.vec.Vec.is_empty`, `Vec.pop`,
   `SharedAVec…into_iter`, `Vec…into_iter`, `…map`, `…collect`) and `copath_loop` (a `loop_spec_measure`
   walk). Mirror the existing admitted Vec contracts.
2. **`sibling` panic-freedom on each element** is the crux: `collect (map sibling fp2)` runs
   `sibling` (→ `parent` → shift + `from_tree_index`) on every node of `fp2`. This panics unless
   each node is a valid non-root tree node (`level < log2 size`, value `< 2^31−1`). So you must
   **strengthen `direct_path`'s postcondition** from `True` to characterise its output vector's
   elements (each a `ParentNodeIndex` with `level ≤ log2 size − 1`, value `< 2^(d+1)`), then carry
   that through `is_empty`/`pop`/`copath_loop` to `fp2`, then a `sibling_noPanic` lemma per element.
   `direct_path_loop_spec`'s invariant already tracks `tones`/bounds — extend it to also accumulate
   a `∀ e ∈ vec, …` element predicate (the pushed `par` values satisfy it via `parent_new_spec`).

## Notes
- Trusted base lives in `FunsExternal.lean` (opaque stdlib axioms) + the admitted `@[spec]` contracts
  in `AdmittedCoreSpecs.lean`. `is_multiple_of` and the Vec/iterator ops are the trusted surface —
  review for faithfulness.
- lean-lsp `lean_goal`/diagnostics can show STALE goals mid-edit; trust `lake build`.
- `parent_new_tti_spec` (full `new>>=parent>>=to_tree_index`) was proved but UNUSED — DELETED in the
  refactor (direct_path uses the par-returning `parent_new_spec`).
