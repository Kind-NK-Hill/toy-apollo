# Phase2 Step 6 Source Proof Route Extraction Plan

Created: 2026-05-24
Status: finalized Step 6 source-route extraction plan; first-batch Step 6A completed; strict Step 6B landed for `prob_10_6`; statement-boundary cleanup landed for `thm_11_7` and `thm_13_14`

## Finalization Result

This plan is the natural Step 6 transition after the Step 5 decision freeze.
Step 5 selected the first Textbook Complete proof targets; this Step 6 plan
extracts source proof routes before any Lean implementation so the project does
not confuse a plausible target with an implementable theorem route.

The finalized transition is:

1. Step 5 freezes target selection and non-target boundaries.
2. Step 6A extracts source proof routes with no Lean proof edits.
3. Step 6A marks each selected target as `ready_for_lean`,
   `needs_statement_decision`, or `defer_open_debt`.
4. Step 6B edits Lean only for targets marked `ready_for_lean`.

This separation is mandatory. A Step 6A blocker is a valid Step 6 outcome for a
target; it must not be forced into Step 6B proof implementation.

Execution result:

- `docs/modification_0525_steps/phase2_step6_source_route_extraction_results.md`
- First-batch Step 6A was completed for `prob_10_6`, `thm_11_7`, and
  `thm_13_14`.
- Strict Step 6B landed for `prob_10_6`.
- `thm_11_7` and `thm_13_14` had their private axioms removed, with final
  assembly moved to theorem-level lemmas. Their missing source proof steps are
  now explicit public premises, so both remain `open_math_debt` rather than
  `textbook_proof_completed`.

## Scope

Step 6 starts from the frozen Step 5 decisions in:

- `docs/modification_0525_steps/phase2_step5_textbook_complete_decision_record.md`
- `docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json`
- `docs/modification_0525_steps/phase2_step6_textbook_complete_proof_work_queue.md`

Step 5 selected exactly three first-batch Textbook Complete targets:

1. `prob_10_6`
2. `thm_11_7`
3. `thm_13_14`

Step 6 is not a new broad cleanup pass. It must not reopen the accepted adapter
set, the deferred Ch14 debts, or the Step 5 non-targets.

## Execution Conventions: Skills And Subagents

Step 6 keeps the project convention that multi-target Phase2 work uses explicit
skills and subagents. The convention is part of the operator protocol, not proof
evidence.

Subagent policy: bounded per-target delegation only; no scope expansion.
Every subagent handoff must preserve the frozen Step 5 decisions, the Step 6A/6B
gate order, and the no-silent-assumption rule.

Required skills by stage:

- Before judging a source route, use `investigation-first` style discipline:
  read the source text, current Lean file, classification row, and relevant
  earlier-chapter declarations before deciding feasibility.
- During route selection, use `contradiction-analysis` only if a target has
  competing routes or unclear statement sufficiency.
- During implementation planning, use `subagent-driven-development` when two or
  more selected targets or independent review tasks can proceed separately.
- Before claiming any extraction or implementation status complete, use
  `verification-before-completion`: run the relevant checks and report their
  actual result.

Required subagent roles:

- `source-route-extractor`: one fresh subagent per target may inspect textbook
  proof steps and produce the Step 6A route note. It must not edit Lean.
- `lean-interface-scout`: a read-only subagent may inspect existing Lean
  declarations, imports, and reusable theorem seeds for a target. It must not
  decide proof completion by name reuse alone.
- `implementation-worker`: only after a target is `ready_for_lean`, a worker
  subagent may edit the target Lean file and directly required local
  bridge/foundation files.
- `spec-reviewer`: after any route note or Lean implementation, a reviewer
  checks compliance with this plan, Step 5 decisions, and source proof route.
- `quality-reviewer`: after spec review, a reviewer checks metadata hygiene,
  proof-surface cleanliness, and validation coverage.

Subagent write-scope rule:

- Step 6A subagents are read-only and write no files unless explicitly assigned
  a route-note file.
- Step 6B implementation subagents must have disjoint write scopes.
- No subagent may edit `project_ledger.json`.
- No subagent may promote an adapter, private axiom, or setup structure to
  Textbook Complete without theorem-level Lean evidence and controller review.

Every Step 6 report should name which skills were used and which subagent roles
were assigned or intentionally skipped.

## Does Step 6 Edit Lean?

Yes, but not immediately.

Step 6 has two gates:

1. **Step 6A: Source proof route extraction.** No Lean proof implementation.
   Extract the textbook proof route, match it to current Lean declarations, and
   decide whether the current theorem statement is strong enough.
2. **Step 6B: Scoped Lean implementation.** Edit Lean only for a target whose
   Step 6A extraction has a feasible route under the frozen Step 5 decision.

If Step 6A shows that a target needs stronger hypotheses, a statement rewrite,
or a new foundation outside the selected route, do not force the Lean proof.
Return that target to `needs_statement_decision` or `open_math_debt` with a
concrete blocker.

## Baseline Rule

The repository is currently dirty from Step 1-5 work. Before any Step 6B Lean
edit, either:

- create an authorized checkpoint commit; or
- record a fresh `git status --short --untracked-files=all` snapshot in the
  Step 6 report and explicitly state that Step 6 is running on a dirty baseline.

## Step 6 Preflight

Run before route extraction and again before any Lean edit:

```powershell
git status --short --untracked-files=all
python -m json.tool docs/phase2_completion_classification.json > $null
python -m json.tool docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json > $null
python tools/validate_phase2_completion_classification.py
python -m unittest tests.test_phase2_completion_classification
python -m unittest tests.test_phase2_clean_debt_surface_audit
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

## Step 6A Extraction Output

For each selected target, produce a route note before Lean edits. The note must
record:

- source proof steps from the textbook;
- current blocker private axiom;
- existing Lean declarations that already prove part of the route;
- missing theorem-level lemmas;
- statement sufficiency check;
- earlier-chapter reuse opportunities;
- whether Mathlib is being used as a local tool or replacing the source route;
- implementation decision: `ready_for_lean`, `needs_statement_decision`, or
  `defer_open_debt`.

Recommended file:

- `docs/modification_0525_steps/phase2_step6_source_route_extraction_results.md`

This file now exists and is the controlling Step 6A result record for the first
batch.

Recommended per-target route-note schema:

```text
task_id
assigned_subagents
skills_used
source_locations_checked
current_blocker_private_axiom
existing_lean_landings
missing_lean_lemmas
statement_sufficiency
mathlib_role
implementation_decision
decision_reason
validation_commands
```

## Target 1: `prob_10_6`

Former blocker before the 2026-05-24 statement-boundary cleanup:

- `ToyApollo/Output/prob_10_6.lean:58`
- `prob_10_6_singleton_masses_to_distribution_internal`

Frozen Step 5 route:

- Build theorem-level countable-space singleton-mass to bounded-test
  distribution bridge.
- Use `tv_distance_core` and `prob_14_5` only as proof seeds, not as current
  closure.

Source route to extract:

1. Easy direction: bounded-test convergence implies singleton masses by testing
   against `1_{x}`. This is already theorem-level in
   `prob_10_6_singleton_masses_of_countableSampleDistribution`.
2. Reverse direction: assume singleton masses converge for every `x`.
3. For a finite set `F`, prove convergence of finite sums of point masses on
   `F`.
4. Use probability mass outside `F` to control bounded test functions on the
   tail.
5. Choose finite `F` with small `μ(Fᶜ)` using countability and probability
   mass.
6. Use finite-sum convergence to show `μn(Fᶜ)` is eventually small.
7. Split integrals over `F` and `Fᶜ`; finite part converges, tail part is small
   by boundedness.
8. Conclude bounded-test integral convergence.

Likely Lean lemmas to land:

- finite-set mass convergence from singleton convergence;
- finite-tail probability control for countable probability measures;
- bounded-function tail integral bound;
- finite-support integral convergence;
- final bridge theorem replacing
  `prob_10_6_singleton_masses_to_distribution_internal`.

Statement sufficiency check:

- Current assumptions include `[Countable Ω]`, `[MeasurableSingletonClass Ω]`,
  and probability measures. Check whether they are enough to make all finite
  subsets measurable and to derive the required integral bounds.
- If the measurable-space interface is too weak, Step 6A must record the exact
  missing assumption instead of adding it silently.

Acceptance criterion:

- Remove `prob_10_6_singleton_masses_to_distribution_internal`.
- Keep the public theorem free of `Bridge` or `Support` parameters.
- `lake env lean ToyApollo/Output/prob_10_6.lean` passes.

## Target 2: `thm_11_7`

Former blocker before the 2026-05-24 statement-boundary cleanup:

- `ToyApollo/Output/thm_11_7.lean:244`
- `thm_11_7_tail_summability_internal`

Frozen Step 5 route:

- Formalize the fourth-moment expansion and tail-summability estimate at theorem
  level.

Source route to extract:

1. Reduce to centered variables `Y_i = X_i - μ`.
2. Expand `E[(Y_1 + ... + Y_n)^4]`.
3. Use independence and zero means to kill mixed terms:
   `E[Y_i Y_j Y_k Y_l]`, `E[Y_i Y_j Y_k^2]`, and `E[Y_i Y_j^3]`.
4. Bound fourth-power terms by the uniform fourth-moment bound.
5. Bound paired square terms by Cauchy-Schwarz:
   `E[Y_i^2 Y_j^2] ≤ sqrt(E[Y_i^4] E[Y_j^4])`.
6. Derive `E[S_n^4] ≤ n c + 3 n (n - 1) c`.
7. Apply Markov to get
   `P(|S_n| / n > ε) ≤ 3c / (n^2 ε^4)`.
8. Prove summability over `n`.
9. Use the already formalized Borel-Cantelli / Theorem 10.1 tail route.

Likely Lean lemmas to land:

- centered-variable independence and mean-zero bridge;
- fourth-moment finite-sum expansion or a bounded expansion theorem;
- mixed-term zero lemmas from independence;
- Cauchy-Schwarz product bound for second-square products;
- Markov fourth-power tail bound;
- p-series summability bound;
- final theorem replacing `thm_11_7_tail_summability_internal`.

Statement sufficiency check:

- Current statement uses `def_5_10_randomVariables P X`, common mean, and
  centered fourth-moment bound. Check whether this gives the measurability and
  integrability needed for all moment expressions.
- If not, do not add hidden hypotheses. Record whether Step 5 must reopen the
  statement with explicit integrability or `MemLp` prerequisites.

Acceptance criterion:

- Remove `thm_11_7_tail_summability_internal`.
- Keep the existing Borel-Cantelli / `thm_10_1` final assembly.
- `lake env lean ToyApollo/Output/thm_11_7.lean` passes.

## Target 3: `thm_13_14`

Current blocker:

- `ToyApollo/Output/thm_13_14.lean:327`
- `thm_13_14_conditional_expectation_internal`

Frozen Step 5 route:

- Formalize interval Fubini, marginal/conditional density calculation, and
  generator extension as theorem-level lemmas.

Source route to extract:

1. Define `h(y) = ∫ g(x) f_{X|Y}(x|y) dx`.
2. Show the defining conditional-expectation identity on sets
   `ℝ × [a,b]`.
3. Use the joint density law to rewrite the two set integrals as density
   integrals.
4. Apply Fubini/Tonelli using integrability of `|g(x)| fXY(x,y)`.
5. Use the definition of marginal density `fY(y)`.
6. Use `fX|Y(x|y) = fXY(x,y) / fY(y)` and `fY(y) ≠ 0`.
7. Obtain equation (13.16) for all closed intervals.
8. Build the π-λ extension from closed intervals to all Borel sets on the
   y-axis.
9. Translate all y-axis Borel sets to `σ(Y)`-measurable vertical cylinders.
10. Conclude the defining property of conditional expectation.

Likely Lean lemmas to land:

- closed-interval cylinder integral identity;
- Fubini/integrability bridge for `g(x) * fXY(x,y)`;
- marginal-density rewrite lemma;
- conditional-density rewrite lemma;
- π-λ/generator extension lemma for closed intervals;
- vertical-cylinder to `σ(Y)` set criterion;
- final theorem replacing `thm_13_14_conditional_expectation_internal`.

Statement sufficiency check:

- Current assumptions may be too weak: `thm_13_14_jointDensityLaw`,
  `Measurable g`, `Integrable (fun z => g z.1) P`, and
  `fY(y) ≠ 0` may not provide all measurability/integrability facts needed for
  Mathlib Fubini and density rewriting.
- Step 6A must decide whether this can be proved under the current statement or
  whether Step 5 must be reopened for explicit density regularity assumptions.

Acceptance criterion:

- Remove `thm_13_14_conditional_expectation_internal`.
- Land interval-Fubini and π-λ obligations on actual theorem/lemma declarations.
- Keep `thm_13_14_identity` routed through the proved main theorem.
- `lake env lean ToyApollo/Output/thm_13_14.lean` passes.

## Step 6B Implementation Rules

Only after a target is marked `ready_for_lean`:

- edit only the target Lean file and directly required local bridge/foundation
  files;
- remove the blocker private axiom only after the replacement theorem compiles;
- update `phase2_prompt_packs/<task_id>/proof_obligations.json`;
- update `docs/phase2_completion_classification.json` and Markdown;
- run target Lean validation and global audit/classification checks.

Do not:

- prove a different theorem than the frozen Step 5 route;
- add source-level assumptions silently;
- promote Mathlib-backed adapter status to Textbook Complete;
- touch deferred tasks such as `prob_10_5`, `prob_11_6`, `prob_11_9`,
  `thm_14_5`, or `thm_14_7`.

## Step 6 Completion Criteria

Step 6A is complete for a target when:

- Step 6A route extraction exists and matches the source text;
- the note records skills used and subagent roles assigned or skipped;
- the note identifies the current private axiom blocker;
- the note lists existing Lean landings and missing theorem-level lemmas;
- the statement sufficiency check is explicit;
- the route is marked `ready_for_lean`, `needs_statement_decision`, or
  `defer_open_debt`;
- the route note is validated against the frozen Step 5 decision.

Step 6B is complete for a target only when:

- the target was first marked `ready_for_lean` in Step 6A;
- the private axiom is removed;
- replacement theorem-level lemmas compile;
- metadata lands on real theorem/lemma declarations;
- the target Lean file builds;
- global classification and audit checks pass.

Step 6 is complete for the batch when all three selected targets have completed
Step 6A and are either:

- upgraded through Step 6B to `textbook_proof_completed`; or
- explicitly returned to `needs_statement_decision` / `open_math_debt` with a
  concrete source-route blocker.
