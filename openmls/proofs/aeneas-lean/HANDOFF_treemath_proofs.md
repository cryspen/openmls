# Handoff — treemath panic-freedom proofs

File: `Openmls/Proofs/Proofs.lean` (Aeneas→Lean). Goal: discharge the 9 `.spec.proof`
obligations for `binary_tree::array_representation::treemath`. Builds green:
`lake build Openmls.Proofs.Proofs`.

## Done (7/9 obligations + helpers, all standard axioms except where noted)
- `level.spec.proof` — post is the strengthened `res ≤ 31 ∧ (res = 0 ↔ index&1 = 0)`.
- `root.spec.proof` — uses `native_decide` once (via `one_le_one_shiftLeft_mod`), so it pulls in
  `Lean.ofReduceBool`; everything else is `propext/Classical.choice/Quot.sound`.
- `left.spec.proof`, `right.spec.proof`, `is_node_in_tree.spec.proof`.
- Helpers: `new_spec` (TreeNodeIndex.new total), `one_le_one_shiftLeft_mod`,
  `level_char` (`level index = n → index % 2^(n+1) = 2^n − 1`).

## Remaining `sorry` (4 loop-based obligations)
`direct_path.spec.proof`, `copath.spec.proof`, `common_direct_path.spec.proof`,
`lowest_common_ancestor.spec.proof`. All post = `⌜True⌝` (pure panic-freedom + termination).

## Trusted-base change already made
`FunsExternal.lean`: `core.num.U32.is_multiple_of` was an opaque `axiom`; it is now a faithful
`def` (`ok (decide (x.val % y.val = 0))`). Needed for `TreeNodeIndex.new` panic-freedom.

## Plan for the remaining 4 (each ≈ `level_char`-sized)
1. **`u32_new` round-trip**: `(do t ← TreeNodeIndex.new x; TreeNodeIndex.u32 t) = ok x`.
   `unfold new/u32/from_tree_index/to_tree_index; simp only [_root_.core.num.U32.is_multiple_of];
   by_cases hx : (↑x:Nat) % 2 = 0 <;> simp_all` leaves two checked-U32 `Result` equations
   (`(x/2)*2 = ok x` even; odd analogue) — evaluate the `div`/`mul`/`sub` (NOT `scalar_tac`; that
   doesn't do raw `Result` equations — try converting to a `Triple` + `step`, or UScalar op specs).
2. **`parent_spec`**: precondition `x1 := u32 x < 2^31 − 1` (⇒ `level x1 ≤ 30` via `level_char`,
   since `level = 31 → x1 = 2^31−1`). Panic-free (oddness of `(x1|2^k)^(b<<(k+1))` follows from
   `level.post`: `k=0` → `2^k` sets bit 0; `k≥1` → iff gives bit 0 = 1). Post must give
   `level (to_tree_index result) = level x1 + 1` (bit analysis: result has `k+1` trailing ones)
   and the value bound — needed for `direct_path`'s measure.
3. **`root` exact value** `(root size).u32 = 2^(log2 size) − 1` (for the walk reaching `r`).
4. **`direct_path`**: `hax_mvcgen [direct_path, TreeNodeIndex.u32, LeafNodeIndex.u32,
   LeafNodeIndex.to_tree_index, TreeSize.u32, TreeSize.leaf_count, MAX_TREE_SIZE] <;> (try scalar_tac)`
   leaves the `root`-value VC + the `direct_path_loop` while-loop. Loop:
   `loop.spec_decr_nat` with `inv := x < 2^31−1 ∧ level x ≤ d`, `measure := d − level x`,
   using `parent_spec` (level+1) and `root` value. `copath`/`common_direct_path` reuse `direct_path`.
5. **`lowest_common_ancestor`**: its own four `loop`s (`loop0..loop3`) over i32 + `from_tree_index`
   validity; tackle last.

## hax_mvcgen idioms (also in memory `reference_aeneas_proof_patterns`)
- Put spec-less helpers AND the spec's `.pre`/`.post`/`.u32` getters/`MAX_TREE_SIZE` in the
  `hax_mvcgen [...]` list (it processes Triples in hypotheses like `h_pre`; `level.post`'s nested
  `lift` otherwise causes a "VC goal target contains but is not equal to the mvar" error).
- `_root_.core.num.U32.is_multiple_of` (the `_root_.` prefix) for `simp/unfold` under `open CoreModels`.
- `cases <arg>` before `hax_mvcgen` when the function/pre `match`es on it.
- Loop bridge: `mspec (Aeneas.Std.WP.spec_to_mvcgen hspec)`; if posts match it closes, else
  `mrename_i hh; mpure hh; mpure_intro` to weaken.
- The hax_mvcgen bug from earlier is fixed; specs are inlined into the `.spec.proof` statements.
