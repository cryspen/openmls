# HANDOFF — treemath panic-freedom development (consolidated 2026-07-31)

Single source of truth for session state. Companion docs: `../../README.org` (user-facing
status + obligation table + module layout), `Openmls/Issues/` (upstream reproducers, now with
stage bisections), `Openmls/Proofs/Experiment.lean` (self-contained spec-shape sandbox).
Work dir: `openmls/proofs/lean/`.

## State (verified 2026-07-31, gate run by orchestrator)

- **DEVELOPMENT COMPLETE.** Gate `~/.elan/bin/lake build Openmls.Proofs.Proofs`
  (lake at `~/.elan/bin/lake`, ~50–90s): **GREEN, 0 errors. 19/19 obligations proved.**
- **Sorry census = exactly the 10 admitted contracts in `AdmittedCoreSpecs.lean`.** Nothing
  else in the tree is sorried. NEW audit fact: `root`/`left`/`right` need ZERO admitted
  contracts (their cones are trio-only, plus bv LRAT certificates for `left`).
- Extraction state: unchanged since the 2026-07-28 regeneration (bool-encoded pres/posts,
  `Result Bool` + `.holds` — note `.holds` is an ABBREV for a triple, so `.holds` goals are
  mvcgen-steppable; inclusive `MAX_TREE_SIZE = 2^30 − 1`; `level` body = `trailing_ones()`,
  no loop, no obligation; `to_tree_index` ×2 / `leaf_count` transparent). Generated files
  build AS GENERATED; `FunsExternal.lean` hand-maintained.
- **Valid-mask migration (2026-07-30/31, landed)**: `TreeSize.valid_mask_spec` is THE
  registered spec — characterization `1 ≤ s ∧ s ≤ 2^30 − 1 ∧ (↑s) &&& (↑s + 1) = 0`.
  The `Nat.log` fixpoint shape survives in exactly one place: `private
  TreeSize.valid_log_characterization` (PartialSpecs), through which the mask spec is proved.
  ALL quarantine preambles (`set L`/`clear_value`, `clear` gymnastics, heartbeat caps) are
  GONE from `root`, `direct_path.spec_pure`, `inc`, `dec`, `common_direct_path`. Consumers
  use `obtain ⟨L, hL⟩ := all_ones_of_and_succ_eq_zero _ (by omega) hmask` (fresh existential
  = the structural quarantine replacement) + `log2_two_pow_sub_one` for body-`log2` residues.
- **One spec theorem per constant**: seven plain triples `MAX_TREE_SIZE/MIN_TREE_SIZE/
  MAX_TREE_INDEX/MAX_LEAF/MAX_PARENT/MAX_LEAF_COUNT/MAX_ROOT_INDEX.spec_value` (@[spec], in
  Proofs.lean right after the raw attribute block). The willYield `MAX_*_mvcgen_spec` layer
  is deleted; the constants are out of the raw attribute block.
- **bv_decide POLICY (user ruling 2026-07-29)**: authorized; per-theorem
  `*._native.bv_decide.ax_*` axioms acceptable. Strict elaboration-time bounds still apply
  (a bv call > ~2s fails). Current bv users: `left.spec.proof` (4 native axioms) via
  `level.spec_bv` (unregistered mask companion, erasure-consumed) + `bv_of_one_shiftLeft_mod`
  (hand-applied through a `key` wrapper) + `@[bvify] ofNat_val_div_two` (the one registered
  bvify rule — unconditionally sound for U32 vals) + `bv_tac 32`.
- `right.spec.proof` / `parent.spec.proof` remain on the Nat routes (`right_bits` /
  `parent_bits_val`); `right` still has 4 case blocks with 16–21-name `rename_i` padding.
- **`subst_vals`** (Common): name-free, class-based substitution of `↑x = e` machine-value
  equations; works on inaccessible hypotheses; occurs-check makes it quarantine-safe; keeps
  (fully-substituted) equations whose scalar is still live in the goal.
- **scalar_tac divergence bisected** (Issues updated, PR-ready): the diverging stage is the
  `Simp.simpAll` preprocessing pass (core `simp_all` loops on self-referential/cyclic
  hypothesis-equation systems; maxSteps never fires — depth, not steps; runtime exceptions
  uncatchable by `try`/`first`). Workaround: `scalar_tac (simpAllMaxSteps := 0)` — proves
  both reproducers. No live divergence trigger remains in the tree post-migration.
- **`Experiment.lean`** (~2400 LOC, imports only Extraction, gate-independent): sandbox with
  copies of everything + V4 result — a consumer-tailored `level` post (8 omega-ready clauses
  incl. both xor VALUES in extracted syntax) closes `left` AND `right` with
  `hax_mvcgen [f, level.spec_v4, - level.spec_pure(, - f.spec.proof)]` +
  `all_goals (subst_vals; scalar_tac)` @ 400k heartbeats, NO case blocks, NO bv axioms.
  **The porting candidate** (user validation pending).
- Loop lemmas unchanged and proved (`lca_loop0_spec`, `common_direct_path_loop_spec`,
  `direct_path_loop_spec` with the positional tones clause).
- Cleanup (2026-07-31): dead chain deleted (`left_bits_lt`, `xor_two_pow_of_(not_)testBit`,
  `ofNat_one_shiftLeft_mod`, earlier `ptti_ok`/`mul2_ok`/`max_*_eq`/`left_val_arith` etc.);
  `triple_of_partialSpec` consolidated into Common; PartialSpecs' `triple_of_ok` renamed
  `triple_of_ok_willYield` (shadowing defused); comments compressed, stale claims fixed
  (the cdp "scalar_tac diverges" note was empirically retested before deletion).

## Architecture (user-ruled — do not deviate without their validation)

- **One theorem per obligation**, statements verbatim 1:1 with
  `Openmls/Extraction/ProofObligationsExplicit.lean` (hand-derived reference, not imported,
  proofs stay `sorry` there).
- **Import DAG / file charters** (README has the table):
  `Common ← BitMath ← {MissingCoreSpecs, AdmittedCoreSpecs, PartialSpecs} ← PureSpecs ← Proofs`
  (PartialSpecs additionally imports BitMath — conforms to the documented DAG).
  Common: loop driver + triple helpers (`loop_spec_measure`, `triple_noThrow_exists_ok`,
  `triple_of_ok`, `triple_of_partialSpec`), `vecLen`, `subst_vals`. BitMath: pure-Nat/u32 bit
  lemmas (`tones`, parent/right value arithmetic, mask↔all-ones conversions, the bvify
  bridges) + registrations. MissingCoreSpecs: PROVED core/alloc contracts (+ the
  `Aeneas.Std` `@[step]` upstream-PR candidates). AdmittedCoreSpecs: the 10 TRUSTED
  contracts. PartialSpecs: treemath spec-vocabulary mvcgen triples + partialSpec
  combinators. PureSpecs: value triples of the transparent fns + monadic helpers (`lca_*`) +
  pure list lemmas. Proofs: the 19 obligations, loop machinery (USER RULING: stays here),
  companion specs, the constants' `spec_value` triples, `sibling_pre_leaf/parent`, the raw
  `attribute [spec]` block.
- **Transparency ruling**: `to_tree_index` ×2 / `TreeNodeIndex.u32` / `leaf_count` carry
  exactly ONE `@[spec]` each — the value-carrying mvcgen triples in PureSpecs.
- **Registered-spec landscape** (fires in every mvcgen): PartialSpecs `valid`/`u32`/`log2`
  triples — NOTE `TreeSize.valid` decide-shape is NOW THE MASK
  `1 ≤ s ∧ s ≤ 2^30 − 1 ∧ (↑s) &&& (↑s+1) = 0` (consumers must match); Proofs' seven
  `*.spec_value` constant triples; `level.spec_pure` (registered; `level.spec_bv` and
  `parent.spec_value`/`direct_path.spec_pure` unregistered, erasure-consumed);
  MissingCoreSpecs proved specs; AdmittedCoreSpecs `slice_iter_all_spec` registered,
  map/collect contracts NOT (hand-applied — playbook 9); BitMath `@[scalar_tac]` rules
  (`level_ge_one(')`, `log2_le_30_or`, `one_le_one_shiftLeft_mod_or`) — never register on a
  bare `2 ^ e` pattern (measured regression, negative result recorded on
  `two_pow_le_u32_max_or`); ONE `@[bvify]` rule (`ofNat_val_div_two`).

## Playbook (hard-won; violations have cost at least one slice each)

1. **Folded-post trap**: `unfold f.pre f.post` before `hax_mvcgen [f]`.
2. **scalar_tac hazards** (reproducers + stage bisection in `Openmls/Issues/`): the
   diverging stage is `Simp.simpAll`; self-referential (`s = 2^(Nat.log 2 s + 1) − 1`) or
   CYCLIC hypothesis-equation systems make it loop with an UNCATCHABLE maxRecDepth.
   No live trigger remains in the tree (mask migration), but when one appears:
   (a) `scalar_tac (simpAllMaxSteps := 0)` is the cheap fix (loses simpAll's Bool-chain /
   decide work — per-site judgement); (b) fresh-existential destructuring
   (`obtain ⟨L, hL⟩ := all_ones_of_and_succ_eq_zero …`) beats `set L`/`clear_value` — named
   hypotheses don't shift `rename_i` arities; (c) `subst_vals` is occurs-check-safe;
   (d) goals with `2^(Nat.log 2 s + 1) − 1` numerals: explicit lemmas; (e) huge-triple
   contexts (copath-scale): omega with materialized bounds.
3. **decide-pairs**: term-level only (`decide_eq_decide.mpr`, `decide_eq_false`,
   `of_decide_eq_true`); never simp a decide-vs-decide.
4. **Never `cases`-split into a folded monadic hypothesis** (whnf blowup). `cases x` BEFORE
   mvcgen is fine. `casesm* _ ∧ _` is the name-free way to split conjunctive posts.
5. **Erasure recipe**: `mvcgen [the_spec, - registered_competitor, <unfolds>]` — the ONLY
   per-call-site override of a registration. **Self-spec hazard**: proofs of registered
   obligations can be discharged CIRCULARLY by their own registration — carry
   `- <self>.spec.proof`, and DETECT via axiom audit: a green build proves nothing; foreign
   axioms in `lean_verify` (e.g. bv axioms in a proof that never called bv) are the tell.
6. **Exact forms**: `IScalar.toNat` not `.toNat`; `UScalar.size UScalarTy.U32` not
   `U32.size` (rfl-equal, not syntactically); `↑x`/`x.bv.toNat` are rfl-equal; `vecLen v`
   is rfl-equal to `v.1.length`; write `v.1`/`v.val`, never `(↑v : List T)`;
   omega treats `2^k` and `&&&` as opaque atoms — pair mask facts with `pow_succ` haves and
   give EXPLICIT bounds on pow atoms (products: generalize via `obtain ⟨Q, hQ⟩ : ∃ Q, … = Q`);
   `native_decide`/bv leak `_native…ax_*` axioms (now policy-acceptable for bv, still avoid
   in reusable Nat helpers).
7. **Statement first**: diff a failing obligation's STATEMENT against
   `ProofObligationsExplicit.lean` before debugging tactics. Then ONE `lean_goal`
   (no column) at the mvcgen line — never guess `rename_i`/`case` arities. Case tags
   DUPLICATE across constructor branches (positional first-match).
8. **Multi-step admitted contracts are INERT in mvcgen lists** — hand-apply via
   `triple_noThrow_exists_ok` + `rw [← Std.Do.WP.bind, hv]` (`← bind_assoc` ×k only on
   shape mismatch; copath's final trio needs none). Close `(wp⟦ok v⟧ …).down` with `trivial`.
9. **`into_vec` stepping**: `simp only [alloc.slice.Slice.into_vec]` THEN
   `mvcgen [alloc.slice.Dummy.into_vec, rust_primitives.sequence.seq_from_boxed_slice,
   alloc.vec.from_seq]` (the Dummy twin exists in no source file — don't grep).
10. **Verification tooling**: trust `lake build` over the LSP; after edits to an imported
    file, ONE `lean_build` MCP call before working downstream (stale-olean trap).
    `lean_diagnostic_messages` unusable while the file errors — per-theorem verification is
    `lean_verify` (axiom list) + `lean_goal` at the last tactic line. `lean_multi_attempt`
    doubles as a redundancy probe. Timing is an ACCEPTANCE CRITERION (user ruling): grind
    conversions were measured and reverted; prefer bounded tactics; the
    `set_option maxHeartbeats 100 in all_goals try scalar_tac` fail-fast sweep is the idiom.
11. **Elaboration-order trap in `have := lemma _ _ (by tac1) (by tac2)`**: `by` blocks run
    left-to-right AFTER unification of explicit args; a side-condition tactic can fire
    before its metavariables are pinned. Fix: a local `key`-wrapper re-exporting the lemma
    with the unifying hypothesis FIRST (named-args, `?holes`, and lambda tricks all fail —
    enumerated in the 2026-07-30 session).
12. **bvify/bv_decide limits** (measured): `bvify` cannot lift cross-width symbolic-exponent
    hypotheses (`↑v % 2^(↑k+1) = …`, `k : Usize`) nor `1 <<< j % UScalar.size` (the
    unconditional lift is FALSE — `↑j = 2^32`; conditional rules are dead weight at bvify's
    `maxDischargeDepth 0`). Hand-bridge via `bv_of_one_shiftLeft_mod`; Nat-indexed BitVec
    shifts are NOT blastable — use `BitVec 32` shift amounts. bv route trades +native axioms
    for shape-insensitivity; on already-linear residues scalar_tac is faster.
13. **Representation switches forfeit the rule ecosystem**: the registered saturation rules
    pattern-match the CURRENT spec shapes (char form, mask form). Changing a spec's shape
    without porting its rules moves their work to every call site (measured on
    `level.spec_bv`: the massert lost `level_ge_one` and cost 12 hand lines). Port rules
    with shapes.
14. **Agent-revert hazard**: never accept "restored byte-identical" from a slice — the
    orchestrator gate caught a revert that DELETED `level_ge_one(')` (breaking `right`
    two theorems away). Gate after every slice, no exceptions.

## Parked / open decisions

1. **Port V4 from `Experiment.lean`** (user gate): retires `right`'s four padded case
   blocks, `left`'s bv plumbing + 4 native axioms, `level.spec_bv`, and orphans
   `right_bits`/`right_val_arith`/`right_val_le`. Cost: `level.spec_v4` is
   consumer-coupled by design; 400k heartbeats per consumer.
2. `root`'s 12-line obtain block: fine as-is; an ∃-form valid characterization was never
   tested (Experiment guidance notes it).
3. `two_pow_le_u32_max_or` (BitMath): textually dead, kept as the recorded
   `@[scalar_tac 2^e]` negative result — delete or keep, user call.
4. `AdmittedCoreSpecs` comment fixes (user-gated): garbled header sentence;
   `deref_mut_slice_spec` docstring says "Not `@[spec]`" but the attribute is present.
5. Trusted-surface shrink (10 → ~7): model `all`/map/collect concretely; `vec_push_spec`
   provable modulo the vecLen/Seq question. Related: root/left/right already need zero
   admitted contracts.
6. **Rust-side spec rewrite (SHELVED, Lean half pre-done)**: mask forms for
   `TreeSize::valid` (`s & (s+1) == 0`) and `level`'s ensures; `log2`/`leading_zeros`
   shift-form specs; would align extraction with the landed Lean mask specs.
7. Upstream queue: the two scalar_tac issues — now bisected to the simpAll stage with
   workaround controls in `Openmls/Issues/` (also a core-Lean `simp_all` divergence
   control), PR-ready; `trailing_ones` CoreModels model+spec; MissingCoreSpecs PR;
   bvify gap (`% UScalar.size` shift lifting); `tones` → `trailing_ones` rename (user);
   spurious hax_lib const; Rust-side `direct_path` positional/level clause.

## Process norms (user-imposed, standing)

- Orchestrator + sub-agents (model ≠ Fable — Opus; EVERY Lean proof edit goes through an
  agent verified via lean-lsp MCP; orchestrator scopes, dispatches, gates, and may only do
  state restoration of agent damage).
- **HARD 8-minute timebox per agent slice** (user ruling 2026-07-29): orchestrator arms a
  timer at launch, TaskStops overruns, and may resume the SAME agent with a ~5-min
  finish-window (stabilize-and-report beats a lost slice; the resume-with-finish-window
  pattern recovered most overruns). Agents must stabilize ~2 min before the buzzer.
- The ORCHESTRATOR runs the authoritative gate after every slice (see playbook 14).
  In-slice verification via lean-lsp MCP only. Lean lookups via MCP, not bash grep
  (grep as a cheap prefilter for reference-counting is OK, `lean_references` confirms).
- Strict proof timing bounds: elaboration time/memory is an acceptance criterion alongside
  greenness (grind-scale blowups get reverted even when green).
- Serialize editors per file; read-only recons may run parallel.
- User validation gates: new specs of any kind, registrations, admitted-surface changes,
  Rust edits, deleting user-authored content. Status report every ~15 min; pause at
  work-package boundaries. No git mutations (user commits).
- Upstream issues → `Openmls/Issues/`, one per file, intentionally failing, imported by
  nothing. `Experiment.lean` is the sandbox: imports only Extraction, gate-independent,
  registrations file-local — spec-shape experiments go there first.
