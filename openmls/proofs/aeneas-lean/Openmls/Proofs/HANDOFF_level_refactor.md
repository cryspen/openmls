# Handoff — treemath panic-freedom proofs: adapt to the new `level.post`, build nicer infra

State as of 2026-07-14. Gate: `lake build Openmls.Proofs.Proofs` (run from
`/home/cblaudeau/openmls/main/openmls/proofs/aeneas-lean`). **Currently RED** — 4 obligations broken
by a fresh re-extraction; the rest compile (some with `sorry`).

## The big picture / direction

We strengthened the Rust spec of `level` so the **trailing-ones characterization travels with the
extracted `level.post`**, and we're using that to **build cleaner proof infrastructure**. The old
approach — a sprawling `tones`-based helper library in `BitMath.lean` (`tones_mod`, `tones_parent`,
`tones_le_30`, `tones_pos_of_odd`, `parent_val_u32`, `parent_bitops_eq`, `parent_lt`,
`small_of_tones`, `trailing_unique`, `parent_val_arith`, …) plus hand-rolled `level_char` /
`level_tones_eq` bridges — is **bloated**. Now that `level`'s ensures *is* the characterization
`r ≤ 30 ∧ index % 2^(r+1) = 2^r − 1`, consumers should get it directly from the registered
`level.spec` (via `mvcgen`) and finish with small, `scalar_tac`-friendly lemmas — not by re-deriving
through `tones`. **Prefer the lean path; retire `BitMath` tones helpers as they become unused.**

## What changed recently (context)

1. Rust `level` (`openmls/src/binary_tree/array_representation/treemath.rs`) ensures is now
   `#[ensures(|r| r <= 30 && index % (1u32 << (r + 1)) == (1u32 << r) - 1)]` (was the weak
   `r ≤ 31 ∧ (r=0 → even)`). Re-extracted, so `level.post` now carries the full characterization.
2. `level_loop_spec` (`Proofs.lean`) STRENGTHENED to match: hypothesis `index < 2^30`, post
   `res ≤ 30 ∧ index % 2^(res+1) = 2^res − 1`, invariant `index % 2^k = 2^k − 1`. **Compiles.**
3. New `@[scalar_tac]` helper `level_ge_one` (`Proofs.lean`, before `level_loop_spec`):
   from the char hypothesis it yields `1 ≤ k ∨ x % 2 = 0`; with `x` odd in context, `scalar_tac`
   then closes the `level x > 0` massert automatically. (Design note: `@[scalar_tac]` only auto-fires
   a **single-premise** lemma whose premise matches the trigger — hence the disjunctive conclusion +
   trigger on the whole char equation. **Compiles.**)
4. Helper `one_shiftLeft_mod_eq (k) (h : k < 32) : 1 <<< k % U32.size = 2^k` moved up so it's in
   scope for the `level` proofs.

**The re-extraction's new `level.post` broke the 4 obligations that feed `level.post` into
`hax_mvcgen`** — this is the fallout to clean up, NOT a regression to hide.

## Obligation status (19 total)

- **Proved (12):** root, lowest_common_ancestor, common_direct_path, is_node_in_tree,
  Leaf/Parent `to_tree_index`, Leaf/Parent `from_tree_index`, `TreeNodeIndex.u32`,
  `TreeSize.{new, inc, dec}`.
- **RED — need re-adapting to the new `level.post` (4):**
  - `level.spec.proof` (~L264): `level_loop_spec` now delivers the exact char (Nat form). Remaining:
    discharge the post's `Result Bool` do-block — the shift form `1<<<n % U32.size` lives in the
    `mvcgen` *hypotheses* (goals are U32 equalities), so reduce them with `one_shiftLeft_mod_eq`
    *in the hypotheses*, then close by the char. (My goal-side `rw` attempt failed for this reason.)
  - `left.spec.proof` (~L291), `right.spec.proof` (~L299): old proof was
    `hax_mvcgen [left, level.post] <;> scalar_tac`, relying on the OLD weak post. Now: unfold the
    `(level.post x r).holds` the spec hands you into the clean char equation (reduce `1<<<n%size →
    2^n`), which makes `level_ge_one` auto-fire and `scalar_tac` discharge `level x > 0`.
  - `parent.spec.proof` (~L307): the core bit-arithmetic (post `r.u32() < MAX_INDEX = 2^29`). Has 9
    internal `sorry` bullets. Needs the char (now available) + a **tight parent-value bound `< 2^30`**
    (BitMath's `parent_val_lt` only gives `< 2^31` — too weak by 2×; the tight version needs the
    `k = 29` edge handled like `parent_val_lt` handles `k = 30`). Also `from_tree_index` parity/`>0`.
- **`sorry` (3):** `sibling.spec.proof` (~L335, 22 holes — body-level panic-freedom over the
  parent×cmp×left/right branches), `direct_path.spec.proof` (~L371, 5 holes — 3 trivial + 2 loop
  holes needing a `direct_path_loop_spec` that was REMOVED), `copath.spec.proof` (~L392, 2 holes —
  needs the sibling-safety stack: `SiblingSafe`, `copath_loop_spec`, `into_map_collect_sibling_spec`).

Dependency order: `level` → `left`/`right` (+`parent`) → `sibling` → `copath`; `direct_path` needs
its loop spec rebuilt. Suggested: **`level.spec.proof` → `left`/`right` → `parent` → the rest.**

## Files in play (all under `Openmls/Proofs/`)

- `Proofs.lean` (648 lines) — the obligations + helpers (`level_loop_spec`, `level_ge_one`,
  `lca_loop0_spec`, `common_direct_path_loop_spec`, `one_shiftLeft_mod_eq`, `level_even_eq`,
  `mul2_ok`, `lca_tail_aux`). Header has a STATUS block.
- `BitMath.lean` (262 lines) — the **bloated `tones` infra**. Trim/retire as the char-based path
  replaces it. `even_shift_eq_ge_two` here is still used by `lca_loop0_spec`.
- `MissingCoreSpecs.lean` — PROVED core specs: `is_multiple_of_spec`, `leading_zeros_spec`,
  `vec_{len,new,with_capacity}_spec`.
- `AdmittedCoreSpecs.lean` — 12 TRUSTED admitted `@[spec]` contracts (audit surface), incl.
  `deref_mut_slice_spec` (write-back preserves length), `u32_div_ceil_spec`, iterator combinators.
- `Common.lean` — `loop_spec_measure`, triple helpers, `vecLen`, `attribute [spec] uncurry`.
- `Proof_bck.lean` (1014 lines) — OLD pre-refactor proofs. Mine for `mul2_ok`, `lca_tail_aux`,
  `level_even_eq`, and the old `level_char`/`parent_*`/`sibling_noPanic`/`copath_loop_spec` scaffolds.
- `Openmls/Extraction/{Funs,Specs,ProofObligations,Types}.lean` — AENEAS-generated (frozen unless
  re-extracted). `ProofObligationsExplicit.lean` — hand-derived explicit-spec reference view.
- Rust source: `openmls/src/binary_tree/array_representation/treemath.rs` (uncommitted edits).

## Hard rules / gotchas

- **Do NOT replace or delete the user's proof bodies with `sorry` without explicit consent** — even
  if they're red. A red build with intact proofs beats a green build with proofs deleted. (This bit
  us; the user was rightly unhappy.)
- The authoritative gate is `lake build Openmls.Proofs.Proofs`. The LSP can disagree / go stale
  mid-edit; trust the build. Each build ≈ 55s.
- Re-extraction is the USER's call — do not run `cargo hax`/charon or change the Rust without
  confirming. `Extraction/*` is generated; `Openmls/Proofs/*` is hand-written.
- `native_decide` is used in several proofs (relies on `Lean.ofReduceBool`) — consistent with the
  existing base; not a hand-written axiom.
- Do not use git to mutate state.
- Techniques reference: `reference_aeneas_proof_patterns` memory; `HANDOFF_treemath_proofs.md`.
