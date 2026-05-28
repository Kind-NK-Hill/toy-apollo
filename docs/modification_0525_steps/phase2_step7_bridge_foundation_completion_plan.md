# Phase2 Step 7 Bridge And Foundation Lemma Completion Plan

Created: 2026-05-25
Status: current Step 7 proof-production entry

## Executive Rule

Step 7 is the first proof-production step after Step 6. It writes Lean, but only
for bridge and foundation lemmas frozen by Step 6. It does not assemble the
final public task theorem unless the selected target itself is an
`interface_bridge_completed` task.

Step 7 exists to prevent this failure mode:

```text
source route extracted -> proof gets hard -> final theorem gains a new public premise
```

Instead, Step 7 must reduce the missing route into theorem-level lemmas. A Step
7 pass may not end with only a prose diagnosis.

## Inputs

Read before starting:

- `docs/modification_0525_steps/phase2_step6_contract_gated_textbook_completion_plan.md`
- `docs/modification_0525_steps/phase2_step6_source_route_extraction_results.md`
- `docs/modification_0525_steps/phase2_step7_bridge_foundation_work_queue.md`
- task-local `phase2_prompt_packs/<task_id>/proof_obligations.json`
- the target Lean file under `ToyApollo/Output/<task_id>.lean`
- relevant earlier ToyApollo outputs and local bridge files named by Step 6

## Allowed Results

Every Step 7 target must end in exactly one of these result classes:

- `foundation_lemma_landed`: at least one named theorem/lemma frozen by Step 6
  was added or repaired, the touched Lean files build, and the corresponding
  obligation contract points to that theorem/lemma.
- `statement_patch_landed`: a statement or bridge-interface change was accepted
  because the frozen signature was impossible or ill-typed; all affected Lean
  files and metadata were updated and build.
- `hard_blocked_with_failed_lean_attempt`: a concrete Lean attempt was made
  against a frozen signature, failed for a specific missing API/theorem/type
  mismatch, and the failed attempt is recorded in a report without being left as
  broken source code.

These are not valid Step 7 results:

- `analysis_complete`;
- `route_blocker_found`;
- `returned_to_open_math_debt`;
- `needs_decision` without a failed Lean attempt or landed statement patch;
- metadata-only cleanup;
- a wrapper theorem that assumes the frozen foundation lemma as a premise.

## Write Scope

Default write scope is narrow:

- target file: `ToyApollo/Output/<task_id>.lean`;
- directly required local bridge/foundation file when Step 6 names one;
- task-local `phase2_prompt_packs/<task_id>/proof_obligations.json`;
- `docs/phase2_completion_classification.json` and Markdown only when the
  classification changes because a real lemma landed or a statement patch was
  accepted;
- Step 7 report files under `docs/modification_0525_steps/`.

Do not edit `project_ledger.json` by hand.

## Proof-Production Rules

For each selected foundation lemma:

1. Copy the exact frozen theorem signature into the Step 7 report.
2. Try to implement the smallest useful lemma first.
3. If the lemma is too large, split it into named sublemmas and land the first
   sublemma that reduces the original obligation.
4. A landed lemma must not take the same obligation as a public premise.
5. A landed lemma may use Mathlib for local facts, but must not be reclassified
   as textbook completion unless it proves the frozen source-route step.
6. If a statement patch is necessary, make the patch explicit and record why the
   original frozen signature was not implementable.
7. If blocked, remove any broken Lean code and record the exact failed theorem,
   error shape, missing declaration/API, and files inspected.

## Validation

For every touched target:

```powershell
lake env lean ToyApollo/Output/<task_id>.lean
python tools/validate_phase2_obligation_contracts.py --task <task_id>
python tools/validate_phase2_completion_classification.py --require-proof-contract
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

If a helper bridge file outside the target file is edited, run Lean on that file
as well.

Do not require global obligation-contract clean status. Step 5.6 owns the global
backlog.

## Current Priority

Start with one target at a time. The recommended first Step 7 target is
`thm_11_7`, because its first productive unit can be smaller than the full
Fubini/generator-extension route in `thm_13_14`.

Preferred first `thm_11_7` unit:

```lean
theorem thm_11_7_pseries_tail_bound ...
```

or, if the current file already has enough tail infrastructure:

```lean
theorem thm_11_7_markov_fourth_tail_bound ...
```

Do not start by attempting the entire
`thm_11_7_tail_summability_from_fourth_moment` theorem unless the required
measurability, integrability, independence, and moment APIs are already found.

## Completion Criteria

A Step 7 pass is complete only when:

- the selected frozen signature is named;
- the result is one of `foundation_lemma_landed`,
  `statement_patch_landed`, or `hard_blocked_with_failed_lean_attempt`;
- touched Lean files build, or failed Lean attempts are removed and documented;
- task-local obligations and classification are updated only to the level
  supported by real Lean evidence;
- the Step 8 handoff is updated if enough foundation lemmas now exist for final
  target assembly.
