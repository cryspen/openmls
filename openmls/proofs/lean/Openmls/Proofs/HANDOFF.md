# HANDOFF — treemath panic-freedom development (consolidated 2026-07-28)

Single source of truth for session state. Supersedes and replaces all previous
`HANDOFF_*.md` files (level_refactor, parent, proof_repair, treemath_proofs,
treemath_reextraction, treemath_refactor — all deleted; their still-relevant content is here).
Companion docs: `../../README.org` (user-facing status + obligation table),
`Openmls/Issues/` (upstream reproducers). Work dir: `openmls/proofs/lean/`.

## State (verified 2026-07-28 ~15:30 CEST — POST-RE-EXTRACTION, repair in progress)

The Rust specs were reworked (user) and the extraction REGENERATED (user, 12:45): `MAX_TREE_SIZE =
2^30 − 1` (inclusive), `level` body = `trailing_ones()` (no loop, no obligation), `to_tree_index`
×2 / `leaf_count` transparent (no posts), `parent` pre gains `≠ MAX_ROOT_INDEX` with 2-clause post,
`left`/`right` have REAL generated posts, `TreeNodeIndex.new` has a pre, pres/posts are BOOL-encoded
(`Result Bool` + `.holds`, `import Hax`), `direct_path.post` is `iter().all` closure form, `copath`
body rewritten (vec![leaf] + append + slice-iter map/collect). **Census: 19 obligations** (was 21).

- **Extraction + spec layers ALL GREEN**: `Extraction.{Types,Funs,FunsExternal,Specs}`,
  `Proofs.{Common,BitMath,MissingCoreSpecs,AdmittedCoreSpecs,PartialSpecs}`.
  - `FunsExternal.lean` gained: `trailing_ones` as a real MODEL (`Nat.find` lowest-clear-bit,
    = `tones` definitionally); axioms slice-iter `map`, slice-iter `all` (`(Bool × Iter T)`);
    `collect`'s FnMut witness made type-generic (extraction mixes `Aeneas.Std` FnMut via
    `BuiltinFnMut` and `CoreModels` FnMut at the same axiom's two call sites).
  - `MissingCoreSpecs.lean`: NEW proved `trailing_ones_spec` (`⇓ r => ↑r = tones ↑x`), 2-line
    proof; file now imports BitMath. Upstream-PR candidate.
  - `PartialSpecs.lean`: `MAX_TREE_SIZE` value spec → `1073741823`; `TreeSize.valid` decide-shape
    now `≤ 2^30 − 1` (all consumers must match this shape).
  - `Specs.lean` builds AS GENERATED — the frozen-hand-override era is over.
- `ProofObligationsExplicit.lean` REWRITTEN (19 theorems, 0 errors, sorries by design). 10 real
  posts: root, left, right, parent, direct_path, TNI.{new,u32}, TS.{new,inc,dec}; 9 `True` posts.
- NEW `Proofs/PureSpecs.lean`: `direct_path.spec_pure` STATEMENT (membership form + positional
  `tones (2·e+1) = i+1` clause for copath's popped-root case), 1 sorry, UNREGISTERED, not yet
  imported anywhere. **Statement awaits user validation** (clause 3 exceeds the Rust post).
- **`Proofs.lean`: 18 of 19 obligations PROVED, exactly 1 error** — `copath.spec.proof`
  (~line 701, `hax_mvcgen` fails on the new deref/slice-iter body; PARKED at the user's stop
  line, next work package). Repair slices R1-R4b (2026-07-28 afternoon) fixed: root + TNI.new
  (R1 — TNI.new's STATEMENT was stale, missing the new pre), parent.spec.proof + sibling (R2 —
  case tags now DUPLICATE across TreeNodeIndex constructor branches, positional matching),
  TS.inc (R3 — uniform "−2 binders" rename_i drift; the 2^29 bound now routes through validity),
  left + right (R4/R4b — RESTATED to the real generated posts and proved via new XOR value
  lemmas). SORRIED (intended): direct_path.spec.proof + PureSpecs' direct_path.spec_pure.
- **Cleanup slice C1 done (user-ordered)**: Proofs.lean 1698 → 1139 lines. Comments trimmed
  (tombstones/battle narratives deleted; hazard notes compressed to ≤2-4 lines). Non-spec
  helpers MOVED OUT (private dropped): 11 pure/bit lemmas → BitMath.lean end section
  (left/right_val_arith, left_bits_lt, right_bits, right_val_le, parent_bits_val,
  parent_val_lt_two_pow_30, eq_root_of_tones_eq, tones_lt_of_ne_root, parent_val_lt_size,
  level_res_eq_zero); 3 monadic helpers → PureSpecs.lean (mul2_ok, lca_tail_aux, lca_level_one).
  Loop machinery STAYS in Proofs.lean (user ruling).
- **File-layout changes (2026-07-28)**: PureSpecs.lean now also hosts the transparent-function
  value triples (to_tree_index ×2, TNI.u32, leaf_count — MOVED from PartialSpecs, single @[spec]
  each, user ruling "single spec attribute, home them in PureSpecs"); PartialSpecs' partialSpec
  combinators were DE-PRIVATIZED for cross-file use; Proofs.lean imports PureSpecs.
- Admitted surface: 12 contracts in `AdmittedCoreSpecs.lean` (unchanged). For the next package:
  `deref`/`Vec.append`/`Slice.iter` are REAL CoreModels defs (specs provable in
  MissingCoreSpecs); only `all` and slice-iter `map`+`collect` (our FunsExternal axioms) need
  ADMITTED contracts — drafts presented to user at the stop-line report, awaiting validation.
- R-slice playbook additions: check the STATEMENT against ProofObligationsExplicit before
  debugging tactics; `lean_goal` at the mvcgen line for binder counts (never guess);
  lean_diagnostic_messages is UNUSABLE while the file has any error — use lean_verify (axiom
  list, no sorryAx) + lean_goal (`goals_after: []`) per theorem; `case tag n₁…nₙ` names the
  LAST n inaccessible hypotheses (like rename_i); omega treats `2^k` as an atom (safe where
  scalar_tac loops) but needs products generalized (`∃ Q, … = Q`) and explicit upper bounds on
  pow atoms; `native_decide` in helpers leaks a `_native…ax` axiom — use scalar_tac.

## Architecture (user-ruled, do not deviate without their validation)

- **One theorem per obligation**, 1:1 with `ProofObligationsExplicit.lean` (hand-derived
  reference, not imported, proofs stay `sorry` there). Extraction files
  (`Extraction/{Types,Funs,Specs}.lean`) are FROZEN hand-overridden generated code — never
  regenerate without re-applying overrides (`Specs.lean` `direct_path.post` is hand-rewritten;
  the old `TreeNodeIndex.new.post` override is retired since the Rust bool-encoding).
- **Stepping = `hax_mvcgen`** (fallback plain `mvcgen` + local massaging); residual goals must
  be pure arithmetic. **Loop invariants are separate named defs** + one `*_loop_spec` per loop
  via `Common.loop_spec_measure`.
- **Registered spec landscape** (fires automatically in every mvcgen):
  - `PartialSpecs.lean` (19 `@[spec]` mvcgen-style triples): `TreeSize.valid` (direct-instantiation
    `willYield (decide C) Q` shape), `log2`, `TreeSize.{u32,leaf_count,parent_count}`, 3 index
    `valid`s, `LNI/PNI.u32`, fallible `to_tree_index` pair, `TreeNodeIndex.u32`, 6 `MAX_*` value
    specs; + private combinators (`partialSpec_bind(_fail)`, `partialSpec_imp`, …).
  - `MissingCoreSpecs.lean`: proved totals (`u32_pow_spec`, `leading_zeros_spec`, vec ops, …) +
    `@[spec]` mvcgen triples for CoreModels `pow`/`leading_zeros`/`is_multiple_of` + `@[step]`
    partialSpecs for `UScalar.cast`, 4 shifts, `massert` (upstream-PR candidates).
  - `Proofs.lean` attribute block: raw-def registrations for constants and small helpers.
  - BitMath registrations: `@[scalar_tac Nat.log 2 x] log2_le_30_or`,
    `@[simp] one_shiftLeft_mod_eq_zero_iff`, `@[scalar_tac 1<<<k % U32.size]` rule,
    `@[scalar_tac] level_ge_one(')`. NEVER register on the bare `2 ^ e` pattern (measured
    regression; `two_pow_le_u32_max_or` stays manual).
- **Sorry style**: explicit bullet/case + `-- TODO(arith): …`; bare `all_goals sorry` only when
  ALL residuals are sorried; never a `sorry` inside `first | … |` chains; never sorry a
  wp/triple/`.holds` goal (means stepping is broken). Census may only decrease.

## Playbook (hard-won; violations have cost multiple slices each)

1. **Folded-post trap**: always `unfold f.pre f.post` before `hax_mvcgen [f]` — a folded post
   leaves un-steppable monadic obligations (this alone was the "blows up" quarantine cause for
   parent/root/cdp).
2. **`scalar_tac` hazards** (see `Openmls/Issues/*.lean` for verified reproducers):
   (a) self-referential `Nat.log` hypothesis (`TreeSize.valid`-shaped) ⇒ uncatchable maxRecDepth
   loop — cure: destructure term-level (`of_decide_eq_true`), then
   `set L := Nat.log 2 s; clear_value L` until NO `Nat.log` occurs (exemplar: `root.spec.proof`);
   (b) cyclic hyp graph (`e ← log2 self`, `self ← 2^e − 1`) ⇒ divergence — `clear` the pow hyp;
   (c) goals carrying `2^(Nat.log 2 s + 1) − 1` numerals — use explicit lemmas
   (`UScalar.eq_of_val_eq`, `Nat.log_mono_right`, `Nat.log_pow`) instead. Raising maxRecDepth
   only trades abort for heartbeat timeout.
3. **decide-pairs**: term-level only (`decide_eq_decide.mpr`, `decide_eq_false`,
   `of_decide_eq_true`); never simp a decide-vs-decide.
4. **Never `cases`-split into a folded monadic hypothesis** (whnf timeout — see sibling's
   in-proof comment). `cases x` BEFORE mvcgen is fine and sometimes required (parent.spec_value:
   the dependent match-pre breaks the matcher splitter otherwise).
5. **Erasure recipe** (how to use an unregistered spec at one call site):
   `mvcgen [the_spec, - registered_competitor, <defs to unfold>]`. Explicit-pass WITHOUT the
   erasure does NOT override the registry; `attribute [local spec]` doesn't either.
   Exemplar: `direct_path_loop_spec` uses `[parent.spec_value, - parent.spec.proof,
   TreeNodeIndex.new, LeafNodeIndex.from_tree_index, ParentNodeIndex.from_tree_index,
   vec_push_spec]`.
6. **Exact forms matter**: `IScalar.toNat` not `.toNat`; `UScalar.size UScalarTy.U32` not
   `U32.size` (irreducible_def; pretty-print twins don't unify). `one_shiftLeft_mod_eq` does
   NOT rw against mvcgen-produced `MAX_*` hypotheses — closed numerals via
   `first | decide | native_decide`. `loop_spec_measure`'s `post :=` needs an explicit result
   type ascription. omega is blind to `% U32.size`, `2^…numBits`, `Nat.log` atoms, literal
   coercions — normalize first (`u32_lt_nat`/`usize_lt_nat` in `Common.lean` are the
   scalar_tac-free comparison bridges).
7. **mvcgen self-spec circularity**: when probing an already-registered sorried spec from an
   imported olean, `mvcgen [f]` can discharge `f` with its own spec — keep `unfold f` in the
   proof to prevent rot.
8. `rename_i` with full binder lists is stable while extraction is frozen; shift-result
   hypotheses arrive as BARE equations (not conjunctions) since the re-extraction.

## Pending user decisions / parked items

1. RETIRED: `vec_index_spec` strengthening — the new membership-form `direct_path.post`
   (iter().all) removed the need; `direct_path.spec_pure` (validated) is the consumption route.
2. `copath`/`direct_path` package (STOP LINE): admitted `slice_iter_all_spec` +
   `slice_iter_map_collect_spec` drafts presented 2026-07-28, awaiting user validation; proved
   specs for `deref`/`Slice.iter`/`Vec.append` to be added to MissingCoreSpecs (CoreModels
   real defs); then spec_pure proof from direct_path_loop_spec; then copath.
3. Rust backport (option C part 2): parent's value ensures phrased via in-crate `level`
   (NOT `trailing_ones` — CoreModels has no model). Retires `parent.spec_value` after
   re-extraction. The domain-constants refactor + `TreeNodeIndex::new` off-by-one fix are
   already in `treemath.rs` (user PR upstream: openmls/openmls#2136 for MAX_TREE_SIZE).
4. Upstream contributions queue: `trailing_ones` CoreModels model; file the two `scalar_tac`
   issues (`Openmls/Issues/`, repros ready); the `@[step]`/mvcgen-triple partial specs in
   `MissingCoreSpecs.lean` (PR to Aeneas/hax per README TODO).
5. `sorryAx` localization in parent's closure (name the trusted supplier).
6. `left`/`right` still state weakened `True` posts vs the reference's real posts
   (reference-conformance only; nothing downstream needs the values).
7. Retirement review of now-unused BitMath `parent_*` lemmas — NOT `parent_bits_val`/`parent_lt`/
   `tones_*` (used by parent.spec_value & direct_path_loop_spec); check `parent_val_arith`,
   `parent_val_u32`, `parent_val_lt` usage before deleting anything.

## Process norms (user-imposed, standing)

- Orchestrator + sub-agents (model ≠ Fable; Opus used throughout), one proof task per capped
  slice (8–15 min; timers + TaskStop; stabilize checkpoint ~2 min before the buzzer: revert
  broken work, REPORT — a lost report costs more than a lost leaf).
- In-slice verification via lean-lsp MCP ONLY (`lean_diagnostic_messages` ~2 min/full pass;
  `lean_multi_attempt` is single-line and breaks on stale imports); the ORCHESTRATOR runs the
  authoritative gate after each slice. `lean_build` once at slice start when imports changed.
- Lean definition lookup via MCP, never bash grep. Serialize editors per file (never two
  agents editing `Proofs.lean`); read-only recons may run parallel.
- User validation gates: new specs (pure/value/registered), admitted-surface changes, Rust
  edits, deleting user-authored content. Status report to the user every ~15 min of active
  work. Never replace user proof bodies without consent. No git mutations (user commits).
- Upstream issues → `Openmls/Issues/`, one per file, intentionally failing, imported by nothing.
