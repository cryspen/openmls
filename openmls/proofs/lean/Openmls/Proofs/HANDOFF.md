# HANDOFF — treemath panic-freedom development (consolidated 2026-08-04)

Single source of truth for session state. Companion docs: `../../README.org` (user-facing
status + obligation table + module layout), `Review.org` (critical review of structure/TCB
+ refactoring-campaign status), `Openmls/Issues/` (upstream reproducers, with stage
bisections). Work dir: `openmls/proofs/lean/`.

## State (verified 2026-08-04, gate run by orchestrator on full re-elaboration)

- **DEVELOPMENT COMPLETE.** Gate `~/.elan/bin/lake build Openmls.Proofs.Proofs`
  (~50–60s): **GREEN, 0 errors. 19/19 obligations proved.**
  Expected-warning baseline: 10 `declaration uses 'sorry'` (AdmittedCoreSpecs), 5
  `unusedTactic` (the `guard_goal_nums` idiom in root/left/right/inc/dec), 2
  `unusedSimpArgs` (BitMath); dependency replays may also show 4 upstream `Aeneas/Std`
  sorries — not ours.
- **Sorry census = exactly the 10 admitted contracts in `AdmittedCoreSpecs.lean`.**
- **Statement freeze is MACHINE-CHECKED**: `Openmls/Proofs/Verification.lean` proves 19
  conformance theorems `<fn>.spec.conformance : <fn>.spec args := <fn>.spec.proof args` by
  definitional unfolding against the GENERATED `Specs.lean`. A re-extraction that changes
  any spec breaks the matching conformance theorem. `ProofObligationsExplicit.lean` is no
  longer load-bearing (readable view only). OPEN: the gate command above does not build
  Verification — extend to `lake build Openmls.Proofs.Verification` (or `Openmls`)?
- **Axiom state: every obligation on `{propext, Classical.choice, Quot.sound}`** (+
  `sorryAx` inherited from admitted contracts where consumed). The 2026-08-03/04 campaign
  removed all 6 `native_decide` sites and the whole bv route (left's 4 LRAT natives gone).
- Extraction state: unchanged since the 2026-07-28 regeneration (bool-encoded pres/posts,
  `Result Bool` + `.holds` abbrev, mvcgen-steppable; inclusive `MAX_TREE_SIZE = 2^30 − 1`;
  `level` body = `trailing_ones()`, no loop, no obligation; `to_tree_index` ×2 /
  `leaf_count` transparent). Generated files build AS GENERATED; `FunsExternal.lean`
  hand-maintained.
- **`left`/`right` are on "scheme b" (2026-08-04, user-designed)**: both consume the
  registered general `level.spec_pure` (NO erasure, NO consumer-tailored spec — the interim
  `level.spec_v4` was deliberately deleted) and derive the consumer-specific xor values
  INSIDE their proofs via the pure BitMath lemma `trailing_ones_xor_vals` (hchar-FIRST
  argument order — the unification anchor for anonymous `by assumption` instantiation).
  Proof shape (shared): step; `all_goals set_option maxHeartbeats 1_000 in (try
  scalar_tac)` fail-fast sweep; `guard_goal_nums 4` tripwire; one name-free closer block.
  FAILURE RECIPE: if left/right break after a re-extraction, FIRST diff
  `trailing_ones_xor_vals`' xor clauses against the new extracted body syntax — the
  coupling to left/right's extracted shift/xor spelling lives there by design.
- **Uniform proof style** across root/inc/dec/left/right: no `unfold pre/post` (stepping +
  `simp at *` normalizes), capped sweep, `guard_goal_nums`, anonymous destructuring
  (`have ⟨L, _, …⟩ := valid_mask_destruct …`), bounded closers. CAUTION: anonymous ⟨⟩
  patterns are ARITY-COUPLED — growing a destruct lemma's conclusion breaks its anonymous
  consumers; prefer a companion lemma or site-local `have` over widening.
- **Valid-mask vocabulary**: `TreeSize.valid_mask_spec` (PartialSpecs) is THE registered
  spec — `1 ≤ s ∧ s ≤ 2^30 − 1 ∧ (↑s) &&& (↑s+1) = 0`. Consumers destructure via
  `valid_mask_destruct` (BitMath: fresh `L`, `s = 2^(L+1) − 1`, log bridge, `L ≤ 29`, pow
  bounds, shift residue — one obtain replaces the old per-site preamble); producers certify
  via `valid_mask_intro`. The `Nat.log` fixpoint shape survives only inside `private
  TreeSize.valid_log_characterization`.
- **Spec plumbing single-sourced (2026-08-03)**: one `partialSpec` body walk per core op in
  MissingCoreSpecs (`u32_leading_zeros_partialSpec`, `u32_pow_partialSpec` +
  `u32_pow_partialSpec_total`); the four registered total/mvcgen specs are derivations
  (statements unchanged). USER-RULED DAG EDGE: `PartialSpecs` imports `MissingCoreSpecs`.
  Combinators merged: `partialSpec_weaken` / `partialSpec_bind_fail` (imp/bind deleted).
- **Case-block factoring lemmas** (all unregistered): `parent_bits_pos` / `parent_bits_odd`
  (corollaries of `parent_bits_val`; parent's 8 blocks are 2-liners),
  `lca_shift_ne` (lca's 4 early-return contradictions are one-liners),
  `dropLast_entries_ne_max_root` (unchanged). `right_bits` DELETED;
  `right_val_arith`/`right_val_le` LIVE (consumed by `trailing_ones_xor_vals` — the old
  "orphan" prediction was wrong). `xor_two_pow_of_(not_)testBit` restored to BitMath.
- **Heartbeats (measured 2026-08-04)**: all 8 file-level `maxHeartbeats 1000000` caps
  REMOVED — every declaration passes at the default 200k. The only genuine consumers are
  `left`/`right`'s scoped `set_option maxHeartbeats 400000 in`. `maxRecDepth 2048`
  file-level options remain (out of scope), plus PartialSpecs' scoped `maxRecDepth 8000`.
- **`Experiment.lean` DELETED** (user-ruled 2026-08-04; V4 graduated). It was UNTRACKED —
  not in git history; archive copy only in the 2026-08-04 session scratchpad. If a sandbox
  is needed again: new file importing only Extraction, registrations file-local, imported
  by nothing.
- **`subst_vals`** (Common) is live gate machinery (consumed by left/right): name-free,
  class-based substitution of `↑x = e` equations; occurs-check quarantine-safe.
- Loop lemmas unchanged and proved (`lca_loop0_spec`, `common_direct_path_loop_spec`,
  `direct_path_loop_spec` with the positional tones clause).
- Constants: seven uniform `*.spec_value` triples (@[spec], Proofs.lean; the two `.spec`
  stragglers renamed 2026-08-04).
- AdmittedCoreSpecs header + `deref_mut_slice_spec` docstring fixed (comment-only; ground
  truth: it IS `@[spec]`-registered, nothing lists it explicitly).

## Architecture (user-ruled — do not deviate without their validation)

- **One theorem per obligation** in `Proofs.lean`; the 1:1 statement correspondence with
  the generated `Specs.lean` `.spec` defs is ENFORCED BY `Verification.lean` (build it
  after touching any obligation statement).
- **Import DAG / file charters**:
  `Common ← BitMath ← {MissingCoreSpecs, AdmittedCoreSpecs} `;
  `PartialSpecs` imports BitMath AND MissingCoreSpecs (edge user-ruled 2026-08-03);
  `← PureSpecs ← Proofs ← Verification` (root `Openmls.lean` imports both Proofs and
  Verification).
  Common: loop driver + triple helpers (`loop_spec_measure`, `triple_noThrow_exists_ok`,
  `triple_of_ok`, `triple_of_partialSpec`), `vecLen`, `subst_vals`. BitMath: pure-Nat/u32
  bit lemmas (`tones`, parent/right value arithmetic, mask destruct/intro,
  `trailing_ones_xor_vals`, xor single-bit lemmas) + registrations. MissingCoreSpecs:
  PROVED core/alloc contracts, now layered as partialSpec body walks + derived registered
  specs (+ the `Aeneas.Std` `@[step]` upstream-PR candidates). AdmittedCoreSpecs: the 10
  TRUSTED contracts. PartialSpecs: treemath spec-vocabulary mvcgen triples + partialSpec
  combinators. PureSpecs: value triples of the transparent fns + monadic/pure helpers
  (`lca_*`, `dropLast_entries_ne_max_root`). Proofs: the 19 obligations, loop machinery
  (USER RULING: stays here), `level.spec_pure`, `parent.spec_value`,
  `direct_path.spec_pure`, `sibling_pre_leaf/parent`, the raw `attribute [spec]` block.
  Verification: the 19 conformance theorems (statement freeze), NO attributes.
- **Transparency ruling**: `to_tree_index` ×2 / `TreeNodeIndex.u32` / `leaf_count` carry
  exactly ONE `@[spec]` each — the value-carrying mvcgen triples in PureSpecs.
- **Registered-spec landscape** (fires in every mvcgen): PartialSpecs `valid`/`u32`/`log2`
  triples — `TreeSize.valid` decide-shape is THE MASK form (consumers must match); Proofs'
  seven `*.spec_value` constant triples; `level.spec_pure` (registered; `parent.spec_value`
  and `direct_path.spec_pure` unregistered, erasure-consumed); MissingCoreSpecs proved
  specs (derived, statements frozen); AdmittedCoreSpecs `slice_iter_all_spec` registered,
  map/collect contracts NOT (hand-applied — playbook 8); BitMath `@[scalar_tac]` rules
  (`level_ge_one(')`, `log2_le_30_or`, `one_le_one_shiftLeft_mod_or`) — never register on a
  bare `2 ^ e` pattern (measured regression recorded on `two_pow_le_u32_max_or`); BitMath
  `@[simp]`: `u32_and_one_eq_zero`, `one_shiftLeft_mod_eq_zero_iff`.
  **ZERO `@[bvify]` rules** (the last one deleted 2026-08-04, user-approved; no bv route
  remains in the gated tree).

## Playbook (hard-won; violations have cost at least one slice each)

1. **Folded-post trap**: historical form was `unfold f.pre f.post` before `hax_mvcgen [f]`;
   the current style closes it with `hax_mvcgen [f] <;> simp at *` instead — either works,
   the modern proofs use the latter.
2. **scalar_tac hazards** (reproducers + stage bisection in `Openmls/Issues/`): the
   diverging stage is `Simp.simpAll`; self-referential or CYCLIC hypothesis-equation
   systems make it loop (uncatchable maxRecDepth). No live trigger remains (mask
   migration), but when one appears: (a) `scalar_tac (simpAllMaxSteps := 0)`;
   (b) fresh-existential destructuring beats `set`/`clear_value`; (c) `subst_vals` is
   occurs-check-safe; (d) explicit lemmas for `2^(Nat.log 2 s + 1) − 1` numerals; (e) huge
   contexts: omega with materialized bounds.
3. **decide-pairs**: term-level only (`decide_eq_decide.mpr`, `decide_eq_false`,
   `of_decide_eq_true`); never simp a decide-vs-decide. NOTE: after `simp at *`, failure
   hypotheses arrive as CURRIED implications (`a → b → ¬c`), not `¬ decide … = true` —
   close with `exact h (by …) (by …) (by …)`, not `absurd`.
4. **Never `cases`-split into a folded monadic hypothesis** (whnf blowup). `cases x` BEFORE
   mvcgen is fine. `casesm* _ ∧ _` is the name-free conjunctive splitter.
5. **Erasure recipe**: `mvcgen [the_spec, - registered_competitor, <unfolds>]` — the only
   per-call-site registration override (current users: `direct_path.spec_pure` consumers,
   `direct_path_loop_spec` hand-application; left/right no longer need one). **Self-spec
   hazard**: carry `- <self>.spec.proof` when a proof could match its own registration
   (impossible while proving it — a theorem cannot erase its not-yet-existing self), and
   DETECT circular discharge via axiom audit: foreign axioms in `lean_verify` are the tell.
6. **Exact forms**: `IScalar.toNat` not `.toNat`; `UScalar.size UScalarTy.U32` not
   `U32.size` (rfl-equal, not syntactic); `↑x`/`x.bv.toNat` rfl-equal; `vecLen v` rfl-equal
   to `v.1.length`; write `v.1`/`v.val`; omega treats `2^k` and `&&&` as opaque atoms —
   pair mask facts with `pow_succ` haves and EXPLICIT pow-atom bounds (each distinct
   exponent needs its own bridge: `valid_mask_destruct` carries `2^(L+1) = 2·2^L` but inc's
   `2^(L+2)` needed a site-local `have … := by ring`).
7. **Statement first**: on a failing obligation, check `Verification.lean`'s conformance
   theorem (it pins statement drift mechanically), then ONE `lean_goal` (no column) at the
   mvcgen line — never guess `rename_i`/case arities. Case tags DUPLICATE across
   constructor branches (positional first-match). `guard_goal_nums` after the sweep is the
   standing tripwire (costs one benign `unusedTactic` warning each).
8. **Multi-step admitted contracts are INERT in mvcgen lists** — hand-apply via
   `triple_noThrow_exists_ok` + `rw [← Std.Do.WP.bind, hv]` (`← bind_assoc` ×k only on
   shape mismatch). Close `(wp⟦ok v⟧ …).down` with `trivial`.
9. **`into_vec` stepping**: `simp only [alloc.slice.Slice.into_vec]` THEN
   `mvcgen [alloc.slice.Dummy.into_vec, rust_primitives.sequence.seq_from_boxed_slice,
   alloc.vec.from_seq]` (the Dummy twin exists in no source file — don't grep).
10. **Verification tooling**: trust `lake build` over the LSP; after edits to an imported
    file, ONE `lean_build` before working downstream (stale-olean trap).
    `lean_diagnostic_messages` unusable while the file errors; per-theorem verification =
    `lean_verify` + `lean_goal` at the last tactic line. Timing is an ACCEPTANCE CRITERION
    (user ruling): compare like-for-like (`lake env lean` on scratch copies for A/B —
    absolute build times swing ±20s with machine load; two same-conditions runs beat five
    cross-day ones). `lake` replay is content-hash keyed: `touch` does not force
    re-elaboration.
11. **Elaboration-order trap in `have := lemma _ _ (by tac1) (by tac2)`**: `by` blocks run
    left-to-right AFTER unification of explicit args. Fix: put the UNIFYING hypothesis
    FIRST in the lemma signature (`trailing_ones_xor_vals`' hchar-first order is this rule
    applied at design time; a local `key`-wrapper re-export works when the lemma is not
    ours to reorder).
12. **bv route (RETIRED 2026-08-04, knowledge kept in case it returns)**: `bvify` cannot
    lift cross-width symbolic-exponent hypotheses nor `1 <<< j % UScalar.size` (the
    unconditional lift is FALSE at `↑j = 2^32`; conditional rules are dead weight at
    `maxDischargeDepth 0`); Nat-indexed BitVec shifts are not blastable. If reintroduced:
    hand-bridge lemmas + per-theorem LRAT native axioms (user-authorized 2026-07-29 policy,
    currently unused).
13. **Representation switches forfeit the rule ecosystem**: registered saturation rules
    pattern-match the CURRENT spec shapes. Changing a spec's shape without porting its
    rules moves their work to every call site. Port rules with shapes.
14. **Agent-revert hazard**: never accept "restored byte-identical" from a slice — gate
    after every slice, no exceptions. (Historical: a bad revert deleted `level_ge_one(')`,
    breaking `right` two theorems away.)
15. **Kernel-irreducible numerics**: `decide` gets STUCK on `U32.size`/`U32.max` facts
    (`U32.numBits` does not kernel-reduce). Use `simp [Aeneas.Std.U32.size_eq]` /
    `simp [Aeneas.Std.U32.max_eq]` (or `scalar_tac`); `native_decide` is banned from the
    tree (axiom hygiene — eliminated 2026-08-03).

## Parked / open decisions

1. **Gate extension**: include `Verification.lean` in the invariant gate command
   (`lake build Openmls.Proofs.Verification` or `Openmls`) — currently only the root
   default target builds it.
2. **Trusted-surface shrink (10 → ~4)**: prove `vec_push_spec` (believed provable modulo
   the vecLen/Seq question); convert `min`/`div_ceil`/`cmp` from axiom+admitted-spec to
   model-def+proved-spec (pattern proven by `is_multiple_of`/`trailing_ones`/`reverse`);
   iterator combinators last (CoreModels-style modelling). Highest-value remaining work.
3. `two_pow_le_u32_max_or` (BitMath): textually dead, kept as the recorded
   `@[scalar_tac 2^e]` negative result — delete or keep, user call.
4. Optional style follow-ups: `lca`'s `hnle` family (4 blocks with load-bearing `clear`
   lists — a minimal-context lemma would be MORE robust); `TreeSize.new.spec.proof`
   alignment to the destruct/intro style; scoped `set_option linter.unusedTactic false`
   for the 5 `guard_goal_nums` warnings.
5. **Rust-side spec rewrite (SHELVED, Lean half pre-done)**: mask forms for
   `TreeSize::valid` and `level`'s ensures; `log2`/`leading_zeros` shift-form specs.
6. Upstream queue: the two scalar_tac issues (bisected, PR-ready, `Openmls/Issues/`);
   `trailing_ones` CoreModels model+spec; MissingCoreSpecs PR (incl. the six `@[step]`
   partialSpec candidates); `tones` → `trailing_ones` rename (user); spurious hax_lib
   const; Rust-side `direct_path` positional/level clause; bvify `% UScalar.size` shift
   lifting gap (no longer blocks us — bv route retired — still an upstream gap).
7. `Experiment.lean` durable archiving: the deleted sandbox is only in the 2026-08-04
   session scratchpad; commit it somewhere if wanted before that expires.

## Process norms (user-imposed, standing)

- Orchestrator + sub-agents (model ≠ Fable — Opus; EVERY Lean proof edit goes through an
  agent verified via lean-lsp MCP; orchestrator scopes, dispatches, gates, and may only do
  state restoration of agent damage). Docs (HANDOFF/README/Review) may be orchestrator-edited.
- **HARD 8-minute timebox per agent slice**: orchestrator arms a timer at launch, TaskStops
  overruns, and may resume the SAME agent with a ~5-min finish-window (stabilize-and-report
  beats a lost slice; this recovered every overrun to date). Agents stabilize ~2 min early.
- The ORCHESTRATOR runs the authoritative gate after every slice (playbook 14). In-slice
  verification via lean-lsp MCP only; bash grep as prefilter, `lean_references` confirms
  before any deletion.
- Strict proof timing bounds: elaboration time/memory is an acceptance criterion alongside
  greenness; measure like-for-like (playbook 10) before accepting or reverting.
- Serialize editors per file; read-only recons may run parallel.
- User validation gates: new specs of any kind, registrations (additions AND deletions),
  admitted-surface changes, DAG changes, Rust edits, deleting user-authored content.
  Status report every ~15 min; pause at work-package boundaries. No git mutations (user
  commits).
- Upstream issues → `Openmls/Issues/`, one per file, intentionally failing, imported by
  nothing. Spec-shape experiments: recreate a sandbox on the deleted-`Experiment.lean`
  pattern (imports only Extraction, gate-independent, registrations file-local) — do not
  experiment in gated files.
