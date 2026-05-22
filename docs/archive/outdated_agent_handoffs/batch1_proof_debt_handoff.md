# Batch 2-3 Proof Debt Handoff

Date: 2026-05-20

This file supersedes the old Batch 1 handoff. Batch 1 has already been run to
completion: its ten child obligations reached `COMPLETED`, had successful
build-checks, passed fresh semantic review, and the relevant parent
`proof_obligations.json` entries no longer contain `accepted_as_proof_debt`.

The next LLM should run Batch 2 and then Batch 3 under the same proof-debt
principle: clear debt only by replacing the accepted assumption with local
theorem-level evidence, then passing the normal Phase2 build and semantic review
loop. Do not count a wrapper, stale candidate, support-field restatement, or
green Lean check alone as debt clearance.

## Active Goal

Finish Batch 2, then Batch 3, without stopping after only one or two debts.

Batch 2 is Chapter 11 plus one small Chapter 14 interface debt:

1. `prob_11_4.density_mean_interface`
2. `prob_11_5.tail_summability_support`
3. `prob_11_6.sixth_moment_support`
4. `prob_11_6.tail_summability_support`
5. `prob_11_7.variance_decay_support`
6. `prob_11_8.covariance_decay_support`
7. `prob_11_9.occupancy_moment_calculation`
8. `prob_11_10.continuous_grid_uniformization`
9. `thm_11_7.fourth_moment_expansion_tail_bound`
10. `prob_14_6.obligation_2`

Batch 3 is measure-theoretic extension, Fubini, and conditional-expectation
verification:

1. `ex_13_5_1.rectangle_area`
2. `ex_13_5_1.pi_lambda_extension`
3. `thm_13_14.interval_fubini_calculation`
4. `thm_13_14.pi_lambda_extension`

Each item must be handled as a normal Phase2 child obligation task. If the child
task does not exist yet, create or discover it through the project mechanism
instead of editing the parent theorem and silently leaving a support parameter.

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks <task_id>
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks <task_id> --review-subject candidate
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks <task_id> --review-result <result-json>
```

If review fails, use `review-fix`, repair `draft.lean` or the official output
file according to the current pack state, then return to `build-check`. The build
and review counters are independent, and the hard limit is 15 for either
counter.

## Current Remaining-Debt Snapshot

After Batch 1 completion, a current scan of
`phase2_prompt_packs/*/proof_obligations.json` found 63
`accepted_as_proof_debt` obligations across 27 parent tasks. Do not use the old
2026-05-19 count of 77 as current state; it included Batch 1 debts that are now
closed.

Batch 2 and Batch 3 should be treated as the next working slice because they are
small enough to complete without needing the full Chapter 14 characteristic
function and CLT foundations.

## General Working Rule For Debts

Proof debt is not cleared by making Lean accept a wrapper. It is cleared only
when the old accepted assumption is replaced by source-faithful theorem-level
evidence and then passes the normal Phase2 loop.

Acceptable replacements:

- a real local theorem proving the missing textbook step;
- a source-faithful local bridge from existing ToyApollo declarations to the
  needed statement;
- a thin local wrapper around Mathlib when Mathlib already has the exact
  standard API;
- a shared foundation theorem imported by multiple downstream tasks;
- a decomposition into smaller ledger-visible obligations.

Unacceptable replacements:

- `axiom`, `constant`, `sorry`, or `admit`;
- a support structure field that restates the same debt;
- a theorem whose hard hypothesis is the missing conclusion under a new name;
- a semantic review pass on a stale candidate or stale review basis;
- treating `lake env lean ToyApollo/Output/<file>.lean` alone as proof of
  semantic clearance.

The import rule and the Mathlib rule are compatible: keep the implementation in
ToyApollo's local output/import structure, but use Mathlib APIs in Tao style
when a standard bridge already exists. Add a thin local bridge only when neither
ToyApollo nor Mathlib exposes the exact interface needed.

## Batch 2 Notes

Batch 2 should start from the Chapter 11 problem-set debts because they are
mostly reusable estimates and concrete calculations:

- `prob_11_4.density_mean_interface`: density interface gives the mean value.
- `prob_11_5.tail_summability_support`: summable tail comparison.
- `prob_11_6.sixth_moment_support`: sixth-moment estimate.
- `prob_11_6.tail_summability_support`: Markov plus p-series comparison.
- `prob_11_7.variance_decay_support`: covariance-band variance decay.
- `prob_11_8.covariance_decay_support`: geometric covariance-decay calculation.
- `prob_11_9.occupancy_moment_calculation`: balls-in-boxes second-moment
  calculation.
- `prob_11_10.continuous_grid_uniformization`: finite-grid uniformization.
- `thm_11_7.fourth_moment_expansion_tail_bound`: reusable fourth-moment SLLN
  tail bound.
- `prob_14_6.obligation_2`: small measurability/interface debt for scaled
  variables.

Before editing, inspect the parent output file, the current candidate, and any
existing Chapter 11 helper declarations. For Problem tasks, use the soft
dependency flow if the pack requires it:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks prob_11_1,prob_11_2,prob_11_3,prob_11_4,prob_11_5,prob_11_6,prob_11_7,prob_11_8,prob_11_9,prob_11_10
python .\run_chapter.py --phase 2 --phase2-mode soft-apply --tasks prob_11_1,prob_11_2,prob_11_3,prob_11_4,prob_11_5,prob_11_6,prob_11_7,prob_11_8,prob_11_9,prob_11_10 --selection <selection-json>
```

Then run the normal single-obligation loop for each Batch 2 debt.

## Batch 3 Notes

Batch 3 is not a one-line interface batch. It needs source-faithful
measure-theoretic extension and Fubini work:

- `ex_13_5_1.rectangle_area`: rectangle integral/area computation for
  `[a,b] x [0,1]`.
- `ex_13_5_1.pi_lambda_extension`: extend the rectangle result to the generated
  sigma-field.
- `thm_13_14.interval_fubini_calculation`: Fubini computation on
  closed-interval cylinders.
- `thm_13_14.pi_lambda_extension`: extend interval-cylinder equality to all
  Borel y-sets.

Do not discharge these by carrying a named pi-lambda or Fubini support field into
the final theorem. If a shared extension lemma is needed, build it once as a
local foundation theorem and import it into both `ex_13_5_1` and `thm_13_14`.

## Verification Before Claiming Batch 2 Or Batch 3 Done

Before saying a batch is done, verify all of the following from the current
worktree:

1. Every child obligation in the batch is `COMPLETED` in `project_ledger.json`.
2. Every child has a latest build result with `success=true`.
3. Every child has a fresh semantic review result with `verdict=pass`.
4. The review result corresponds to the current review input/candidate hash.
5. The relevant parent `proof_obligations.json` entries are no longer
   `accepted_as_proof_debt`.
6. Relevant output files contain no active `axiom`, `constant`, `sorry`, or
   `admit` after ignoring comments.
7. Relevant output files do not expose equivalent support assumptions such as
   `hTailSummabilitySupport`, `hPiLambdaExtensionSupport`, or similarly named
   restatements of the exact debt.
8. A final targeted `lake build` covering the affected output modules succeeds.

## Important Process Warning

`ToyApollo/Output` may be ignored by Git in this repository. `git status` is not
enough to know whether output files changed. Always inspect files directly with
`rg`, and verify with `lake env lean` or targeted `lake build`.
