# Handoff — treemath proofs file structure (refactor DONE)

State as of 2026-06-29. Build is **GREEN** (`lake build Openmls.Proofs.Proofs`, run from
`/home/cblaudeau/openmls/main/openmls/proofs/aeneas-lean`). All **9/9** treemath `.spec.proof`
obligations are proved; the only `sorry`s are **11 trusted stdlib `@[spec]` contracts**, now all
purely about `core`/`alloc` (see "Audit surface" below).

Repo note: this work lives in the `main` git worktree (branch `proofs/extraction`); a separate `dev`
worktree exists on its own branch. Do NOT run extraction (aeneas/charon/hax) and do NOT use git.
Edit Lean only; build to verify.

## What changed

The original 1840-line monolith `Openmls/Proofs/Proofs.lean` (five interleaved concerns A–E, in
proof-chronological order) has been split into five coherent modules under `Openmls/Proofs/`. Each
file carries its own preamble (the same `import`s, the four `open`s, the `set_option`s, and
`namespace openmls`).

```
Common.lean            (A) generic infra: loop_spec_measure + the 3 triple helpers
                           (triple_noThrow_exists_ok / _elim / triple_of_ok, now PUBLIC — they are
                           used all over D/E), vecLen / vecLen_eq_length, `attribute [spec] uncurry`
   ↑
BitMath.lean           (B) pure-Nat tones/parent bit lemmas (no monad, no Aeneas types)   ← Common
MissingCoreSpecs.lean  (C-proved)   vec_len_spec, vec_new_spec, vec_with_capacity_spec      ← Common
AdmittedCoreSpecs.lean (C-admitted, THE AUDIT SURFACE) sliceIterElems (opaque) + the 11
                           admitted @[spec] contracts, all generic over `core`/`alloc`        ← Common
   ↑
Proofs.lean            (D) per-function treemath value specs + SiblingSafe (treemath) +
                       (E) the 9 `.spec.proof` obligations            ← Common, BitMath,
                           This file contains NO `sorry`.               MissingCoreSpecs, AdmittedCoreSpecs
```

Import DAG: `Common ← {BitMath, MissingCoreSpecs, AdmittedCoreSpecs} ← Proofs`. `Openmls.lean`
imports `Openmls.Proofs.Proofs` (the build gate); the lakefile globs `roots = ["Openmls"]`, so the
new modules are picked up automatically.

## The audit surface (the only thing a reviewer must trust)

`AdmittedCoreSpecs.lean` is the single file holding every `sorry`. All 11 contracts are now stated
purely in terms of `core`/`alloc` operations — **no treemath symbols** leak in:
`deref_mut_slice_spec` (not `@[spec]`; stepped explicitly), `reverse_slice_spec`, `vec_index_spec`,
`vec_push_spec`, `min_usize_spec`, `u32_cmp_spec`, `sharedavec_into_iter_spec`,
`slice_iter_next_spec`, `vec_is_empty_spec`, `vec_pop_spec`, and the generic
`into_map_collect_spec`. They are the contracts for the bare `axiom`s in `FunsExternal.lean` that
Charon could not extract (Vec ops, the `min`/`cmp` ops, and the lazy iterator combinators
`into_iter`/`map`/`collect`). The opaque model `sliceIterElems` and the proved `MissingCoreSpecs`
specs sit *outside* this file by design.

## Hard constraints the structure preserves (these bite if you move things again)

1. **`@[spec]` registration order.** `mvcgen` uses already-elaborated `@[spec]`s. The dependency
   `common_direct_path.spec.proof` → `direct_path.spec.proof` is preserved because **both stay in
   `Proofs.lean` in their original relative order** (D and E were never reordered among themselves —
   only A/B/C were lifted out). All imported `@[spec]`s register before the `Proofs.lean` body,
   which is a superset of the prior availability, so nothing in D/E lost access.
2. **Mis-/over-firing global `@[spec]`s + ok-equation workarounds** (`level.spec.proof`, `new_spec`,
   `left/right.spec.proof`) all live in `Proofs.lean` and are untouched. Do NOT "simplify" their
   `triple_noThrow_exists_ok` + `rw [← bind_assoc, hOk]; simp [bind_tc_ok]` escapes into direct
   `mvcgen [helper]` — they will break.
3. **`attribute [spec] uncurry`** is registered once in `Common.lean` and propagates to every
   importer (attributes are environment-global across imports). Do not re-add it elsewhere.
4. **`open binary_tree.array_representation.treemath in`** still prefixes the treemath decls in
   `Proofs.lean` (per-decl). `AdmittedCoreSpecs`/`MissingCoreSpecs`/`BitMath`/`Common` need no
   treemath `open` at all.

## Cleanups folded in during the refactor

- **Deleted `parent_new_tti_spec`** (proved but unused — `direct_path` uses `parent_new_spec`).
- **Split the core specs by trust status**: the three *proved* Vec specs went to
  `MissingCoreSpecs.lean`; the *admitted* contracts (the audit surface) went to
  `AdmittedCoreSpecs.lean`.
- **Generalised the only treemath-flavoured admitted contract.** The old
  `into_map_collect_sibling_spec` baked in `sibling`/`TreeNodeIndex`/`SiblingSafe`. It is now a
  generic `core` contract `into_map_collect_spec {T} (v : Vec T) (f : T → Result T)` (admitted, NOT
  `@[spec]`), and the `sibling` instance `into_map_collect_sibling_spec` is **proved** (not admitted)
  in `Proofs.lean` by `into_map_collect_spec fp sibling hsafe` — it kept the same statement and stays
  `@[spec]`, so the `copath` obligation's `mvcgen` is unchanged. `SiblingSafe` (treemath) moved back
  to `Proofs.lean`. Result: the audit surface is entirely `core`-only.

## Notes
- `lean_goal`/diagnostics can be STALE mid-edit — `lake build Openmls.Proofs.Proofs` is the
  authoritative gate (it can disagree with the LSP).
- The 4 other `sorry` warnings in a full build are upstream Aeneas stdlib (`Aeneas/Std/*`), not ours.
- See `HANDOFF_treemath_proofs.md` (same dir) for the final spec of every function + proof
  techniques, and the `reference_aeneas_proof_patterns` memory for the reusable idioms.
