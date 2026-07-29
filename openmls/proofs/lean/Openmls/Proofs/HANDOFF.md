# HANDOFF — treemath panic-freedom development (consolidated 2026-07-29)

Single source of truth for session state. Companion docs: `../../README.org` (user-facing
status + obligation table + module layout), `Openmls/Issues/` (upstream reproducers).
Work dir: `openmls/proofs/lean/`.

## State (verified 2026-07-29, gate run by orchestrator)

- **DEVELOPMENT COMPLETE.** Gate `~/.elan/bin/lake build Openmls.Proofs.Proofs`
  (lake at `~/.elan/bin/lake`, ~50–90s): **GREEN, 0 errors. 19/19 obligations proved.**
- **Sorry census = exactly the 10 admitted contracts in `AdmittedCoreSpecs.lean`** (the whole
  trusted audit surface; was 12 before 2026-07-28). Nothing else in the tree is sorried.
- Extraction state: regenerated 2026-07-28 against the reworked Rust specs — bool-encoded
  pres/posts (`Result Bool` + `.holds`, `import Hax`), `MAX_TREE_SIZE = 2^30 − 1` (inclusive),
  `MAX_ROOT_INDEX = 2^29 − 1`, `level` body = `trailing_ones()` (no loop, no obligation),
  `to_tree_index` ×2 / `leaf_count` verification-transparent (no posts), `parent` pre
  `valid ∧ ≠ MAX_ROOT_INDEX` with 2-clause post, `left`/`right` real posts, `TreeNodeIndex.new`
  has a pre, `direct_path` post in `iter().all` closure form, `copath` body =
  vec![leaf] + slice-iter map/collect + append + into_iter/map(sibling)/collect.
  **Generated files build AS GENERATED** (`Extraction/{Types,Funs,Specs,ProofObligations}.lean`
  — regenerate freely); `FunsExternal.lean` is hand-maintained (axioms + real MODELS for
  `trailing_ones` (= `tones`' `Nat.find`), `is_multiple_of`, `reverse`).
- Loop lemmas all proved: `lca_loop0_spec`, `common_direct_path_loop_spec`,
  `direct_path_loop_spec` (invariant `direct_path_loop_inv` carries a POSITIONAL clause:
  entry `i` has `tones (2·l[i]+1) = i + 1`).
- Companion specs (each user-validated): `level.spec_pure` (REGISTERED; no official level
  obligation exists anymore), `parent.spec_value` (unregistered, erasure-consumed),
  `direct_path.spec_pure` (unregistered, erasure-consumed; clauses: `vecLen ≤ 29`, membership
  bounds `↑e ≤ 2^29−2 ∧ ↑e < ↑size/2`, positional tones clause — feeds direct_path + copath).

## Architecture (user-ruled — do not deviate without their validation)

- **One theorem per obligation**, statements verbatim 1:1 with
  `Openmls/Extraction/ProofObligationsExplicit.lean` (hand-derived reference, 19 entries,
  not imported, proofs stay `sorry` there).
- **Import DAG / file charters** (README has the table):
  `Common ← BitMath ← {MissingCoreSpecs, AdmittedCoreSpecs, PartialSpecs} ← PureSpecs ← Proofs`.
  Common: loop driver + triple helpers (`loop_spec_measure`, `triple_in_hypothesis`,
  `triple_noThrow_exists_ok`, `vecLen`). BitMath: pure-Nat/u32 bit lemmas (`tones`,
  parent/left/right value arithmetic) + scalar_tac/simp registrations. MissingCoreSpecs:
  PROVED core/alloc contracts. AdmittedCoreSpecs: the 10 TRUSTED contracts. PartialSpecs:
  mvcgen/partial-correctness triples for extracted helpers + the (de-privatized) partialSpec
  combinators. PureSpecs: value triples of the transparent fns + monadic helpers
  (`mul2_ok`, `lca_*`) + pure list lemmas (`dropLast_entries_ne_max_root`). Proofs: the 19
  obligations, loop machinery (USER RULING: loop specs/invariants stay here), companion
  specs, sibling `.holds` helpers (`sibling_pre_leaf/parent`, `ptti_ok`, `max_*_eq`), the
  raw `attribute [spec]` block.
- **Transparency ruling**: `to_tree_index` ×2 / `TreeNodeIndex.u32` / `leaf_count` carry
  exactly ONE `@[spec]` each — the value-carrying mvcgen triples in PureSpecs.
- **Registered-spec landscape** (fires in every mvcgen): PartialSpecs `valid`/`u32`/`log2`/
  `MAX_*` triples (NOTE `TreeSize.valid` decide-shape is `1 ≤ s ∧ s ≤ 2^30 − 1 ∧
  s = 2^(log₂ s + 1) − 1` — consumers must match); MissingCoreSpecs proved specs
  (`trailing_ones_spec ⇓ r => ↑r = tones ↑x`, `vec_{len,new,with_capacity,is_empty,pop,
  append}`, `vec_deref_slice`, `slice_iter_of_slice`, `leading_zeros`, `u32_pow`, …);
  AdmittedCoreSpecs: `slice_iter_all_spec` IS registered; `slice_iter_map_collect_spec` and
  `into_map_collect_spec` are NOT (hand-applied — see playbook 9); BitMath registrations
  (never register on a bare `2 ^ e` pattern — measured regression).

## Playbook (hard-won; violations have cost at least one slice each)

1. **Folded-post trap**: `unfold f.pre f.post` before `hax_mvcgen [f]`.
2. **scalar_tac hazards** (reproducers in `Openmls/Issues/`): (a) self-referential `Nat.log`
   hypothesis ⇒ maxRecDepth loop — destructure term-level (`of_decide_eq_true`), then
   `set L := Nat.log 2 s; clear_value L`, `clear` every pow hypothesis before scalar_tac
   (`root.spec.proof` is the exemplar). When NO value from the decide is needed, cheaper:
   `rename_i` it a name and `clear` it. (b) cyclic hyp graphs diverge — clear the pow hyp.
   (c) goals with `2^(Nat.log 2 s + 1) − 1` numerals: explicit lemmas, not scalar_tac.
   (d) scalar_tac can also maxRecDepth near HUGE triple hypotheses (copath-scale contexts):
   use omega with materialized bounds (`v.property : v.val.length ≤ Usize.max`).
   (e) `set L := …` reverts/re-introduces every `Nat.log`-mentioning hypothesis at the END
   of the context — later `rename_i` lists budget +2 slots.
3. **decide-pairs**: term-level only (`decide_eq_decide.mpr`, `decide_eq_false`,
   `of_decide_eq_true`); never simp a decide-vs-decide.
4. **Never `cases`-split into a folded monadic hypothesis** (whnf blowup). `cases x` BEFORE
   mvcgen is fine and sometimes required. The guard
   `first | scalar_tac | (cases i <;> simp_all <;> scalar_tac)` is safe: it can only reach
   pre-VCs (no folded post present).
5. **Erasure recipe**: `mvcgen [the_spec, - registered_competitor, <unfolds>]` — the ONLY
   way to override a registration at one call site. **Self-spec hazard**: any
   `*.spec.proof` whose proof steps its own function must carry `- <self>.spec.proof`
   (the sorried/proved olean registration would discharge it circularly). Weak registered
   posts (root, direct_path) force erasure + the value route (`spec_value`/`spec_pure`).
6. **Exact forms**: `IScalar.toNat` not `.toNat`; `UScalar.size UScalarTy.U32` not
   `U32.size`; `vecLen v` is `rfl`-equal to `v.1.length`; `(↑v : List T)` ascriptions FAIL
   to elaborate — write `v.1`/`v.val`; `loop_spec_measure`'s `post :=` needs an explicit
   result-type ascription; omega treats `2^k` as an opaque atom (safe where scalar_tac
   loops) but needs products generalized first (`obtain ⟨Q, hQ⟩ : ∃ Q, 2^k * (x/2^k) = Q :=
   ⟨_, rfl⟩`) and EXPLICIT upper bounds on pow atoms; closed numerals: `first | decide |
   native_decide` — but `native_decide` in a lemma leaks a `_native…ax_*` axiom into
   lean_verify: prefer scalar_tac/norm_num in reusable helpers.
7. **Statement first**: diff a failing theorem's STATEMENT against
   `ProofObligationsExplicit.lean` before debugging tactics (a stale statement mimics
   tactic failure). Then one `lean_goal` (no column) at the mvcgen line: full VC list with
   binder counts — never guess `rename_i`/`case` arities. Case tags DUPLICATE across
   `TreeNodeIndex` constructor branches (positional first-match: Leaf blocks before
   Parent). `case t n₁…nₙ` names the LAST n inaccessible hypotheses (like rename_i).
8. **Multi-step admitted contracts are INERT in mvcgen lists** (frame matcher only sees
   head calls; single-call triples like `spec_pure` work fine in the list). Hand-apply:
   `have h := <contract> args hsafe; obtain ⟨v, hv⟩ := triple_noThrow_exists_ok h;
   rw [← Std.Do.WP.bind, hv]` — add `← bind_assoc` (×k) ONLY if the do-block shape
   mismatches; for copath's final trio NO bind_assoc is correct. Close `(wp⟦ok v⟧ …).down`
   with `trivial`.
9. **`into_vec` / vec-literal stepping**: `alloc.slice.Slice.into_vec` goes through a
   lifted twin `alloc.slice.Dummy.into_vec` (generated by `@[rust_fun … -lift]`, exists in
   no source file — don't grep). Incantation: `simp only [alloc.slice.Slice.into_vec]`
   THEN `mvcgen [alloc.slice.Dummy.into_vec, rust_primitives.sequence.seq_from_boxed_slice,
   alloc.vec.from_seq]`.
10. **Verification tooling**: trust `lake build` over the LSP; after edits to an imported
    file, ONE `lean_build` MCP call (build + LSP restart) before working downstream —
    the LSP silently serves stale oleans otherwise (even `#check` lies).
    `lean_diagnostic_messages` is UNUSABLE while the file has any error — per-theorem
    verification is `lean_verify` (axiom list; no sorryAx beyond admitted contracts, no
    unexpected `_native…ax_*`) + `lean_goal` at the last tactic line (`goals_after: []`).
    `lean_multi_attempt` doubles as a redundancy probe (`first | current | fallback` —
    "never executed" on the fallback proves current suffices).

## Parked / optional (nothing blocks anything)

1. Cosmetic: promote `ptti_ok` to PureSpecs next to `mul2_ok`; share the `max_*_eq`
   constants (an inline duplicate sits in `direct_path.spec.proof`); delete
   `Proof_bck.lean` (its useful blocks were lifted 2026-07-28); 4 linter warnings.
2. Trusted-surface shrink (10 → ~7): model `all` / slice-iter `map` / `collect`
   concretely (CoreModels-style) — the three composed-iterator contracts become provable.
   `vec_push_spec`: provable from `seq_push` modulo the vecLen/Seq representation question.
3. Upstream queue: `trailing_ones` CoreModels model + spec (proved here, PR-ready);
   MissingCoreSpecs PR; the two scalar_tac issues (reproducers ready in `Openmls/Issues/`);
   `tones` → `trailing_ones` rename (user TODO); spurious hax_lib const; Rust-side
   `direct_path` spec upgrade to carry the positional/level clause (user plans to phrase
   it via `level`).

## Process norms (user-imposed, standing)

- Orchestrator + sub-agents (model ≠ Fable; Opus used throughout), one task per hard
  time-boxed slice (8–15 min normal, up to ~25 on explicit user budget; timers + TaskStop;
  stabilize-and-report ~2 min before the buzzer — a lost report costs more than a lost leaf).
- In-slice verification via lean-lsp MCP ONLY; the ORCHESTRATOR runs the authoritative
  gate after every slice. Lean definition lookup via MCP, never bash grep.
- Serialize editors per file; read-only recons may run parallel.
- User validation gates: new specs of any kind (pure/value/registered), admitted-surface
  changes, Rust edits, deleting user-authored content. Status report every ~15 min of
  active work; pause at work-package boundaries. No git mutations (user commits).
- Upstream issues → `Openmls/Issues/`, one per file, intentionally failing, imported by
  nothing.
