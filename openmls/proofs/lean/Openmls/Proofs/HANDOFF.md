# HANDOFF — treemath panic-freedom development (consolidated 2026-08-04)

Single source of truth for session state. Companion docs: `../../README.org` (user-facing
status + obligation table + module layout), `Review.org` (critical review of structure/TCB
+ refactoring-campaign status), `Openmls/Issues/` (upstream reproducers, with stage
bisections). Work dir: `openmls/proofs/lean/`.

## State (verified 2026-08-04 EVENING, gate run by orchestrator on full re-elaboration)

- **DEVELOPMENT COMPLETE.** Gate `~/.elan/bin/lake build Openmls.Proofs.Proofs
  Openmls.Proofs.Verification` (~50–60s): **GREEN, 0 errors. 19/19 obligations proved.**
  Expected-warning baseline: 2 `declaration uses 'sorry'` (AdmittedCoreSpecs — the two
  `collect` contracts), 5 `unusedTactic` (the `guard_goal_nums` idiom in
  root/left/right/inc/dec), 2 `unusedSimpArgs` (BitMath); dependency replays may also show
  4 upstream `Aeneas/Std` sorries — not ours.
- **Sorry census = exactly the 2 admitted contracts in `AdmittedCoreSpecs.lean`**
  (`slice_iter_map_collect_spec`, `into_map_collect_spec`) — down from 10 via the
  2026-08-04 FunsExternal modelling program + CoreModels upgrade (see the campaign section
  below). `common_direct_path.spec.proof` and the vec/index/push consumers are now
  sorryAx-FREE; only proofs consuming the collect pair inherit `sorryAx`.
- **DEPENDENCY PINS MOVED (2026-08-04, user-instructed)**: `hax`/CoreModels now from
  `https://github.com/cryspen/hax`, branch `openmls-core-models` (resolved `7e43f8a`),
  `subDir hax-lib/proof-libs/lean`; aeneas transitively bumped `52fd438` → `e0961db`.
  Fallout absorbed: (a) WP API rename `Aeneas.Std.WP.{willYield,willFail,willDiverge,
  Result.postShape}` → `Aeneas.Std.*` (partialSpec family KEPT its `WP` namespace) — 46
  sites renamed in Common/MissingCoreSpecs/PartialSpecs/PureSpecs; (b) CoreModels scalar
  `Ord` restructure (`core.mkUOrd`/`mkIOrd` GONE; `cmp` is now a standalone
  `core.<Ty>.Insts.CoreCmpOrd.cmp` def with an if-cascade body) — min_usize/u32_cmp proof
  bodies repaired; (c) `CoreModels.core.num.U32.{leading_zeros,pow}` bodies UNCHANGED —
  the body-walk sections replayed as-is.
- **`FunsExternal.lean` = 1 axiom + 2 models** (was 15 axioms + 3 models this morning):
  the `Map…collect` axiom (the ONE remaining trusted operation) and the two lazy
  `Iterator::map` models (`ok ⟨self, f⟩`). Everything else is deleted — bare names resolve
  to upstream CoreModels twins, and the affected specs were RE-PROVED against the upstream
  bodies (statements frozen). The what-went-where history lives ONLY in this file's
  campaign record (the in-file tombstone comments were removed 2026-08-04, user request). Verified missing
  upstream (do not delete these three): slice-iter `map` and `Map…collect` are absent as
  flat names (upstream instance namespaces have only `next`(+`all`); the generic
  `IteratorMethods` structure has `map`/`all`/`collect` fields but wrong names/shapes for
  the frozen call sites, and its `map` takes `Fn`, not `FnMut`); vec-`IntoIter.map` exists
  in BOTH CoreModels (CoreModels-`FnMut` — application type mismatch with the call site's
  Aeneas `BuiltinFnMut`, verified) and `Aeneas.Std` (right `FnMut`, but hidden by
  `Funs.lean`'s `open … hiding` and returns Aeneas's `Map` type, which doesn't compose
  with the collect reference).
- **Statement freeze is MACHINE-CHECKED**: `Openmls/Proofs/Verification.lean` proves 19
  conformance theorems `<fn>.spec.conformance : <fn>.spec args := <fn>.spec.proof args` by
  definitional unfolding against the GENERATED `Specs.lean`. A re-extraction that changes
  any spec breaks the matching conformance theorem. `ProofObligationsExplicit.lean` is no
  longer load-bearing (readable view only). RESOLVED 2026-08-04: the gate command now
  includes `Openmls.Proofs.Verification` (see the State bullet above).
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
- `AdmittedCoreSpecs.lean` now holds ONLY the two `collect` contracts
  (`slice_iter_map_collect_spec`, `into_map_collect_spec`), both UNREGISTERED
  (hand-applied — playbook 8). `sliceIterElems` moved to `Common.lean` (2026-08-04; the
  only DAG-legal home once `slice_iter_all_spec` migrated — sibling files cannot import
  each other).

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
  `triple_of_ok`, `triple_of_partialSpec`), `vecLen`, `sliceIterElems` (moved here
  2026-08-04), `subst_vals`. BitMath: pure-Nat/u32
  bit lemmas (`tones`, parent/right value arithmetic, mask destruct/intro,
  `trailing_ones_xor_vals`, xor single-bit lemmas) + registrations. MissingCoreSpecs:
  PROVED core/alloc contracts — partialSpec body walks + derived registered specs (+ the
  `Aeneas.Std` `@[step]` upstream-PR candidates); since 2026-08-04 also the whole migrated
  vec/slice/cmp/iterator family, proved against UPSTREAM CoreModels bodies
  (`trailingOnes_bv_eq_tones` and `slice_iter_all_count_spec` are the two nontrivial
  unregistered bridge helpers). AdmittedCoreSpecs: the 2
  TRUSTED contracts (the collect pair). PartialSpecs: treemath spec-vocabulary mvcgen triples + partialSpec
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
  specs (statements frozen; incl. the migrated family — `vec_index_spec` is now pinned to
  the concrete usize `SliceIndex` instance, `deref_mut`/`reverse` carry the 2026-08-04
  restated/strengthened posts); AdmittedCoreSpecs: NOTHING registered (the two collect
  contracts are hand-applied — playbook 8); BitMath `@[scalar_tac]` rules
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
16. **Shadow-deletion falseness audit (2026-08-04, bit us once)**: deleting a shadowing
    axiom flips an admitted contract's subject to a CONCRETE def — a spec that was a
    satisfiable constraint on an axiom can become a sorried FALSE statement (worse than
    the unsatisfiability risk it replaced). Audit every admitted spec whose subject just
    became concrete: vec_index's quantified `SliceIndex` inst (arbitrary `get` ⇒ `ok none`
    ⇒ panic) and deref_mut's `vecLen (back s') = vecLen v` (false of the identity
    write-back) were both caught this way and fixed by USER-APPROVED restatements.
17. **Root-namespace unfolds inside `namespace openmls`**: `unfold core.slice.…` in tactic
    position resolves through `open CoreModels` FIRST — use the `_root_.` prefix to reach
    a root-namespace FunsExternal def. Related: a projection out of a `@[reducible]`
    instance (`…CoreSliceIndexSliceIndexSliceT.get`) is NOT `unfold`-able (no head
    application) but IS `simp only [name]`-reducible. Let-bound fvars in upstream bodies
    (`seq_push`'s `extended`, `all`'s `let s := self`) block `rw`/`List.length_append` —
    `simp +zetaDelta` / `simp only [h]` (zeta-reducing) are the fixes.
18. **Upstream-body re-proof recipe (B1–B3, 2026-08-04)**: when a FunsExternal model is
    deleted in favour of an upstream CoreModels body, keep the spec statement frozen and
    re-prove by: unfold the upstream chain (find it via lean_declaration_file, never
    grep); prefer a single unregistered `partialSpec`/induction helper as the body-walk
    single-source (house convention); monadic sub-ops (`x % y`) often already have
    `@[step]` partialSpecs upstream (`U32.rem_spec`) — case-walk on the Result instead of
    re-deriving. `iterAllCount`-style `brecOn` recursions: `induction l` + `simp
    [CoreModels.core.iterAllCount, …]` on the equations, never raw unfold.

## Parked / open decisions

1. (RESOLVED 2026-08-04) **Gate extension**: the gate command is now
   `lake build Openmls.Proofs.Proofs Openmls.Proofs.Verification`.
2. **Trusted-surface shrink**: EXECUTED to 10 → 2 (see "Campaign record" below). The last
   step (2 → 0) is the collect item — prefer the upstream-PR route over the fuel-drain +
   CallMut design (which remains USER-GATED if chosen).
3. `two_pow_le_u32_max_or` (BitMath): textually dead, kept as the recorded
   `@[scalar_tac 2^e]` negative result — delete or keep, user call.
4. Optional style follow-ups: `lca`'s `hnle` family (4 blocks with load-bearing `clear`
   lists — a minimal-context lemma would be MORE robust); `TreeSize.new.spec.proof`
   alignment to the destruct/intro style; scoped `set_option linter.unusedTactic false`
   for the 5 `guard_goal_nums` warnings.
5. **Rust-side spec rewrite (SHELVED, Lean half pre-done)**: mask forms for
   `TreeSize::valid` and `level`'s ensures; `log2`/`leading_zeros` shift-form specs.
6. Upstream queue: the two scalar_tac issues (bisected, PR-ready, `Openmls/Issues/`);
   **CoreModels iterator PR** (the flat per-instance `SharedAT.map` / `IntoIter.map`
   (FnMut-familied) / `Map…collect` defs — see campaign record; `trailing_ones` model is
   now upstream, its `tones` spec still ours); MissingCoreSpecs PR (incl. the six
   `@[step]` partialSpec candidates); `tones` → `trailing_ones` rename (user); spurious
   hax_lib const; Rust-side `direct_path` positional/level clause; bvify `% UScalar.size`
   shift lifting gap (no longer blocks us — bv route retired — still an upstream gap).
7. `Experiment.lean` durable archiving: the deleted sandbox is only in the 2026-08-04
   session scratchpad; commit it somewhere if wanted before that expires.

## Campaign record: FunsExternal modelling program (EXECUTED 2026-08-04, censuses gated)

Outcome: admitted contracts **10 → 2**; FunsExternal **15 axioms + 3 models → 1 axiom +
2 models**. Trajectory (every slice orchestrator-gated green): 10 →(reverse as-stated)
9 →(Tier-1: 7 shadowing axioms deleted)→(min/cmp proved; vec_index found FALSE-as-stated
and withheld) 7 →(div_ceil + 2 map models; div_ceil proved) 6 →(all model; slice_iter_all
proved; sliceIterElems moved to Common.lean) 5 →(CoreModels re-pin + WP-rename repair;
B1/B2/B3 upstream-body re-proofs) 5 →(USER-APPROVED restatements: deref_mut faithful
identity-write-back form, reverse strengthened to `res.val = s.val.reverse`,
common_direct_path re-closed with ZERO delta) 4 →(USER-APPROVED vec_index specialization
to the concrete usize instance + vec_push as-stated) **2**. All migrated specs
lean_verify on ⊆ {propext, Classical.choice, Quot.sound}, no sorryAx.

Remaining work (the old Tier-3 collect item, REFRAMED by the new CoreModels):
`Map…collect` is the only trusted axiom; its two admitted contracts are the census.
Options: (a) the original fuel-drain model + CallMut typeclass (design still USER-GATED);
(b) upstream now ships a generic `IteratorMethods` structure (fields incl. `map`, `all`,
`collect` — collect drains via the Iterator witness) — an upstream PR adding the flat
per-instance `SharedAT.map` / `IntoIter.map` (FnMut-familied) / `Map…collect` defs in the
Charon naming convention would let us delete everything left in FunsExternal and prove
both collect contracts against upstream bodies. Prefer (b); it also fixes the
two-FnMut-family seam at `Funs.lean:1254` (Aeneas `BuiltinFnMut` for plain fns vs
CoreModels `FnMut` for closures) that currently forces our IntoIter.map glue model
(Aeneas-`FnMut` parameter, CoreModels-`Map` result).

### Original program design (kept for reference)

Goal was: admitted contracts 10 → 0, `FunsExternal.lean` axioms 19 → ~1–3 never-consulted
witnesses. Trust moves from quantified admitted contracts (unsatisfiability risk) to
readable model definitions (no ⊥ risk; faithfulness auditable by eye). Proved specs MOVE
from AdmittedCoreSpecs to MissingCoreSpecs with their `@[spec]` intact; the gate's expected
sorry census DROPS with each slice — update the baseline per slice, and fix the
AdmittedCoreSpecs header count when it changes. RECON IS DONE (2026-08-04, via lean-lsp
MCP; do not redo with grep) — key facts below.

**Discovery: `FunsExternal.lean` predates current CoreModels; 7 axioms shadow concrete
library defs.** Bare names in generated `Funs.lean` resolve to our ROOT-namespace axioms;
deleting an axiom flips resolution to CoreModels' def (both files `open CoreModels`).

- **Tier 1 (delete 7 shadowing axioms; gate decides):**
  `core.Usize.Insts.CoreCmpOrd` → CoreModels def (Core/FunsPrologue.lean);
  `core.U32.Insts.CoreCmpOrd.cmp` → CoreModels full instance `CoreModels.core.U32.Insts.
  CoreCmpOrd` (FunsPrologue; flat `.cmp` resolves as projection);
  `core.slice.index.SliceIndex` (type) and `core.Usize.Insts.
  CoreSliceIndexSliceIndexSliceT` → CoreModels twins (Core/Funs.lean);
  `alloc.vec.Vec.Insts.CoreOpsIndexIndex.index` → exact-signature flat def
  (Alloc/Funs.lean, delegates to slice index over deref);
  `alloc.vec.Vec.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter` → `ok self`
  (Alloc/Funs.lean); `alloc.vec.into_iter.IntoIter.Insts.CoreIterTraitsIteratorIterator`
  → concrete instance (next via `seq_len`/`seq_remove`).
  Then PROVE (→ MissingCoreSpecs): `min_usize_spec` (CoreModels `core.cmp.min` cases on
  `OrdInst.cmp`, Core/Funs.lean:522), `u32_cmp_spec`, `vec_index_spec`.
  QUICK WIN any time: `reverse_slice_spec` is provable AS STATED today (subject already a
  concrete def) — admitted by inertia only.
- **Tier 2 (trivial models):** `div_ceil` := `if y = 0 then fail else ok (x/y + [x%y≠0])`
  → spec provable. Both `map` axioms := `ok ⟨iter, f⟩` (CoreModels `Map I F` is the
  structure `{iter : I, f : F}`, Core/Types.lean:352). `hash` STAYS an axiom (nothing
  constrains it; honest uninterpreted constant).
  **USER-GATED spec restatements**: adopt Aeneas's canonical `deref_mut` model
  (identity write-back — `Aeneas/Std/Vec.lean` `alloc.vec.Vec.deref_mut`); the current
  admitted `∀ s', vecLen (back s') = vecLen v` is FALSE of that model (satisfiable but
  stronger than canonical) — restate faithfully (`s.val = v.val ∧ ∀ s', (back s').val =
  s'.val`), strengthen `reverse_slice_spec` to `res.val = s.val.reverse`, and re-close the
  one consumer `common_direct_path.spec.proof` (reverse preserves length). Present both
  new statements to the user before landing.
- **Tier 3 (real modelling):** `Iter…IteratorSharedAT.all` := recursive short-circuit fold
  over the concrete list (`Iter T` reducibly `Seq T`, Core/Types.lean:826) calling
  `call_mut` (CoreModels `FnMut` = `{FnOnceInst, call_mut : F → T → Result (O × F)}`,
  Core/TypesPrologue.lean:23) → `slice_iter_all_spec` provable by induction.
  `Map…Iterator.collect` — two design points: (a) closure witness is type-generic
  (`FnMutInst : W`, two FnMut families meet there) → `CallMut W F T O` typeclass with two
  instances (Aeneas `Std.core.ops.function.FnMut` incl. the `BuiltinFnMut` route, and
  CoreModels'); instance-implicit is invisible at existing call sites; (b) draining the
  abstract iterator via the passed Iterator witness (`{next : I → Result (Option Item ×
  I)}`) is not structurally terminating → FUEL model (cap `Usize.max`, `div` on
  exhaustion — honest: Rust diverges on infinite iterators). → both map/collect specs
  provable (concrete iterators, fuel ≥ length). `FromIterator` witness: implement via the
  same drain or leave as never-consulted axiom. Independent: prove `vec_push_spec`
  (subject concrete in CoreModels; known fight: mvcgen vs dependent-`if`).

Hard rules for the package: generated `Types/Funs/Specs/ProofObligations.lean` untouched;
every model carries a faithfulness docstring (it IS the new audit surface); one tier-1
deletion batch per slice max; gate + census check after every slice; spec restatements and
registration moves are user-gated as usual.

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
