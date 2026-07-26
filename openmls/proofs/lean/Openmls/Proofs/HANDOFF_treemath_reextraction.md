# Handoff — update the treemath proofs to the re-extracted specs

State as of 2026-07-06. Gate `lake build Openmls.Proofs.Proofs` (from
`/home/cblaudeau/openmls/main/openmls/proofs/aeneas-lean`) is **RED**. A fresh extraction was run
after backporting/cleaning the Rust specs; the hand-written proofs are now stale. This doc is the
plan to bring them back to green.

## What happened

1. `treemath.rs` specs were cleaned up + backported (uncommitted). Summary of the contract changes:
   - `MAX_TREE_SIZE = 2^30` = **max node count**; new `#[cfg(hax)] const MAX_INDEX = MAX_TREE_SIZE/2`
     (= 2^29) = the leaf/parent-number bound. New `valid()` predicates on the three index types.
   - `level`: pre `index < MAX_TREE_SIZE` (was `< 2^31`); post weakened to one direction
     (see below). `root`: pre `0 < s ≤ MAX_TREE_SIZE` (was `≤ 2·MAX-1`).
   - `left`/`right`: pre `index.u32() < MAX_INDEX`. `direct_path`/`copath`/`common_direct_path`:
     size pre `≤ MAX_TREE_SIZE`. `lowest_common_ancestor`/`is_node_in_tree`: `< MAX_INDEX`.
   - `to_tree_index` (Leaf+Parent): pre `self.valid()`; **`ensures` dropped** (no more `= 2p+1`).
     `TreeNodeIndex::new`: round-trip `ensures` dropped. `Parent::from_tree_index`: pre `%2==1`
     (Leaf: none). `TreeSize::inc`/`dec`: new pres.
   - `is_node_in_tree`: `requires` restored (valid-style match); **`ensures` dropped on purpose** —
     the postcondition will be handled with a "special proof technique" (per user), not via `.post`.
   - `direct_path`: added `#[ensures(forall(|i| implies(i<len, 2·e_i+1 < 2^31−1)).and(len ≤ 30))]`.
2. New extraction (07-09 15:30) regenerated `Openmls/Extraction/{Funs,Specs,Types,ProofObligations}.lean`.
   `FunsExternal.lean` was **not** regenerated (trusted axiom base intact → `AdmittedCoreSpecs.lean`
   still valid). Hand-written `Openmls/Proofs/*.lean` are unchanged/stale.

## BLOCKER #1 — fix this FIRST: `Funs.lean` itself doesn't compile (`hax_lib.prop.*` undefined)

`direct_path`'s `forall(|i| implies(...))` ensures extracted into a closure returning
`hax_lib.prop.Prop` and calling `hax_lib.prop.implies` / `hax_lib.prop.Prop.Insts.CoreConvertFromBool`
(`Funs.lean` ~1021–1108). **None of `hax_lib.prop.*` is defined** anywhere in the Aeneas / CoreModels
/ Hax proof-libs (grep confirms). Errors:
```
Funs.lean:1027: Unknown identifier `hax_lib.prop.Prop`
Funs.lean:1039: Unknown identifier `hax_lib.prop.implies`
```
`level`'s parity ensures is a plain `bool`, so it extracted cleanly — **only the `forall`/`implies`
ensures triggers this.** Until this is resolved nothing downstream compiles (so the proof-level
error list below is still partly unknown — rebuild after fixing this).

**Decision needed (pick one):**
- **(A) Provide a Lean model for `hax_lib.prop`** — define `Prop`, `implies`, `forall`, `and`, the
  `From<bool>` instance, and the `Fn/FnMut/FnOnce` closure insts, in a support file imported before
  `Funs`. This is what aeneas `-specs hax` expects. First check whether the *pinned* toolchain ships
  it: the extraction printed **version mismatches** (aeneas expected `e0a1596`, found `157c25e`;
  charon expected `0.1.218`, found `0.1.216` — "run ./install-aeneas.sh"). The missing `hax_lib.prop`
  may simply be because the wrong aeneas/charon/Hax-lib is installed. Pin first, re-extract, recheck.
- **(B) Drop the `forall`/`implies` ensures from `direct_path`** (keep `len ≤ 30` only, or drop the
  ensures entirely) and re-extract. Keep the per-element bound as the existing Lean helper
  `direct_path_elems_spec` (as before the backport). Simplest; removes the `hax_lib.prop` dependency.

Recommendation: try (A) via the toolchain pin (cheap to test); fall back to (B) if `hax_lib.prop`
still isn't provided. Confirm with the user before re-extracting either way.

## Once `Funs.lean` compiles — the proof-level work (rebuild to get the real error list)

Key spec deltas the proofs must now match (obligations are regenerated in `ProofObligations.lean`,
all `:= by sorry`; the real proofs live in `Proofs.lean` and must match the new `.spec`/`.pre`/`.post`):

- **`level.post` changed shape** (`Specs.lean:39`), now one-directional:
  ```
  if r ≤ 31 then (if r = 0 then (index % 2 = 0) else True) else False
  ```
  i.e. `r ≤ 31 ∧ (r = 0 → index even)`. The old proof used the full iff
  `(r==0) == (index even)`; rework `level.spec.proof` to the weaker post. `level_loop_spec`
  (in `Common.lean`) still needs `index < 2^31`; the new pre gives `< 2^30` (stronger) so the
  `hidx` derivation via `scalar_tac` should still go through.
- **`level`/`left`/`right` panic-freedom**: `left`/`right` still need `k = level(x) > 0` before
  `<< (k-1)`. Source: `x` is odd (from `to_tree_index` body — its `ensures` is gone, so keep
  *unfolding* the body, as the current obligation proof already does) + `level.post`'s
  `r = 0 → index even` (contrapositive: odd ⇒ `r ≠ 0`). Re-derive with the new post.
- **`to_tree_index` pre is now `self.valid()`** (`= self.0 < MAX_INDEX`; `MAX_INDEX : Result U32`,
  `Funs.lean:40`; `valid` defs at `Funs.lean:210/400/614`). This precondition now rides on **every**
  call site — `u32`, `left`, `right`, `parent`, `sibling`, `direct_path`, `is_node_in_tree` — so the
  proofs must discharge `self.valid()` (unfold to `< MAX_INDEX`, from the caller's bound). **This is
  the biggest ripple.**
- **`is_node_in_tree`**: obligation is now panic-freedom only (ensures dropped). Its `.u32()` call
  hits `to_tree_index`'s `valid()` pre → discharge from `is_node_in_tree`'s restored pre. The
  functional postcondition is the user's "special technique" (out of scope for the obligation).
- Bounds renamed `2^31` / `MAX_TREE_SIZE/2` → `MAX_TREE_SIZE` / `MAX_INDEX`. Audit helper lemmas
  with hardcoded bounds: `ptti_ok`, `new_u32_eq`/`new_u32_triple`, `parent_tni_spec`/`parent_new_spec`,
  `root_u32_spec`, `direct_path_loop_spec`/`direct_path_elems_spec`, `left_noPanic`/`right_noPanic`,
  `sibling_noPanic`.
- **`direct_path.spec.proof`**: if option (A) kept the `forall` ensures, the per-element bound is now
  part of the extracted `.post` → the obligation must *prove* it (previously it was `True` and we had
  `direct_path_elems_spec` as a standalone helper — fold that in). If option (B), unchanged.

## Files in play
- Stale proofs: `Openmls/Proofs/{Proofs,Common,BitMath,MissingCoreSpecs,AdmittedCoreSpecs}.lean`.
- New extraction: `Openmls/Extraction/{Funs,Specs,Types,ProofObligations}.lean` (07-09 15:30).
  `FunsExternal.lean` unchanged (trusted).
- Rust specs: `openmls/src/binary_tree/array_representation/treemath.rs` (uncommitted).
- Gate: `lake build Openmls.Proofs.Proofs`. `ProofObligations.lean` is a generated `sorry` template
  and is **not** imported by `Proofs.lean` (no clash) — don't import it.

## Reminders
- The trusted base (`AdmittedCoreSpecs.lean`, 11 admitted core contracts) and `BitMath.lean` are
  unaffected by the spec changes and should still compile once `Funs.lean` does.
- This task legitimately involves re-extraction (options A/B both may need it) — coordinate with the
  user; don't re-extract silently.
- Techniques: `HANDOFF_treemath_proofs.md` (final specs + idioms), `reference_aeneas_proof_patterns`
  memory, and `README.org` (current-state overview + TODO).
- Pin the aeneas/charon/Hax toolchain (`./install-aeneas.sh`) before trusting any re-extraction —
  the version mismatch is very likely behind BLOCKER #1.
