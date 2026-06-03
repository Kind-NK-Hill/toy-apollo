# Phase2 Debt Cleanup Playbook

Use this for repairing accepted proof debt or hidden proof-package interfaces.
For the meaning of completion classes, use `proof_fidelity_contract.md`.

## Cleanup Standard

A task is clean only when:

- the Lean file builds;
- the public task-facing theorem has no forbidden proof-package premise;
- public assumption packages do not hide source proof steps;
- proved obligations land on theorem/lemma declarations;
- metadata and classification match the Lean state.

No accepted-debt counter by itself proves cleanliness. For example, a corpus may
have no parent task with `accepted_as_proof_debt > 0` and still fail strict
public-surface audit because a `proof_debt_support` item marked `proved` lands
only on a structure field, support predicate, or blank landing.

## Allowed Internal Scaffolds

Internal `Support`, `Spine`, setup structures, or source packages may be useful
while organizing proof. They are acceptable when they are constructed by local
theorems and consumed internally.

They are not acceptable when the public theorem asks the user to provide them.

## Common Hidden Forms

Watch for:

- `axiom`, `constant`, `private axiom`, `sorry`, `admit`;
- a structure field that restates the missing proof step;
- a theorem whose hard premise is the missing statement;
- a public local package containing `Support`, `Spine`, `Bridge`,
  `ProofBeyondBook`, or theorem-specific proof evidence;
- public assumptions that should have been derived internally.

Public assumptions must be expanded. A theorem can have no visible
`Support`/`Spine` parameter and still hide debt inside a `Setup`,
`SourcePackage`, or local definition.

## Repair Pattern

1. Identify the exact public leak or hidden assumption.
2. Locate the source proof step it represents.
3. Search existing ToyApollo outputs and Mathlib.
4. Prove the missing theorem-level lemma or classify the file honestly as
   adapter/open debt.
5. Make the public theorem assemble internal evidence.
6. Update task-local obligations and classification only after Lean proof
   exists.

If several debt tasks share the same missing bridge, estimate, or interface
translation, create a shared foundation theorem first. Do not solve the same
gap repeatedly with task-local support packages.

For large accepted debt, `promote-obligations` may convert blocking
`proof_obligations.json` entries into `Phase2ObligationTask` ledger children.
The parent remains the official output owner. Completed children stay in the
ledger as history; do not delete them just because the parent proof strategy
later changes. If an obligation split is superseded, close or mark the old
child through the ledger path rather than removing the audit trail.

For sibling child obligations under the same parent, do not generate all review
results first and apply later. Applying one child can change the parent's review
basis and make sibling review results stale. Use a fresh review/apply cycle per
child.

## Lessons

Green Lean is not enough. A file such as
`prob_10_10_distribution_bridge.lean` can compile while using axioms; semantic
cleanup must reject that as proof debt rather than treating compilation as
cleanliness.

Stale pack candidates are dangerous. If an official output was updated, for
example `ToyApollo/Output/ex_13_6_5.lean` moving to
`ex_13_6_5_GamblingTeamProcess`, old pack candidates carrying older assumptions
do not describe the current official output. Regenerate or review the correct
subject before applying a verdict.

Existing output is often the main source of the missing bridge. Before
inventing a new foundation, inspect older task outputs, task-local
bridge/foundation files, Chapter 9 examples such as `thm_9_5`, and downstream
files that already consume the same concept.

Mathlib can supply APIs and atomic facts, but it should not replace the
textbook proof with an unrelated black-box theorem unless the local wrapper
makes the source-step equivalence explicit and the result is classified
honestly as adapter work.

For already completed first-batch foundation work, reusable themes included CDF
convergence to `TendstoInDistribution`, probability convergence from
constant-limit distribution convergence, quantile measurability and quantile
law facts, Chapter 14 weak/distribution interfaces, and optional-stopping
gambling-team process evidence. Reuse these patterns instead of recreating
theorem-local support fields.

Deprecated Batch 4/5/6 "clean" wording is historical context only. Those
batches targeted tightness kernels, Levy/characteristic-function/MGF/Slutsky
bridges, explicit CLT models, triangular arrays, and uniform integrability, but
their old cleared status is not current evidence. Current proof-debt state is
determined by strict audit plus fresh Phase2 build/review/apply evidence.

## Debt Analysis Template

Before editing a debt-bearing task, write down:

- the current public statement and whether it exposes a support/spine package;
- the textbook proof spine or source construction being repaired;
- existing ToyApollo declarations, bridge/foundation files, dependency
  decisions, and Mathlib APIs that may already discharge the step;
- the intended theorem-level landing declaration;
- the replacement for each accepted debt assumption;
- the latest build result, review result, and review basis hash;
- the exact blocker if the repair cannot close.

This template is working evidence for the review gate. It does not replace a
fresh build/review/apply loop.

## Review JSON Discipline

Accepted-debt repairs are especially sensitive to stale or malformed review
results:

- `obligation_review.items[*].obligation_id` must be the parent obligation id
  from the request, not a renamed child id;
- if the review input lists direct downstream consumers, include one
  `downstream_adequacy.consumers_checked` entry for every listed consumer;
- pass results must use schema status values such as `covered` or
  `not_applicable`, not custom strings;
- if `review-apply` says the basis changed, discard the result, run fresh
  `review-now`, write a new result, and apply immediately;
- if `pack` reports that a hard dependency still carries proof debt, clear that
  dependency first rather than editing a stale pack to bypass the dependency
  gate.

## Large Debt

Do not pause merely because a proof is large. Convert it to smaller
ledger-visible obligations when needed:

1. identify the exact source proof steps;
2. check whether each step already exists in output or Mathlib;
3. for each missing step, prove it locally or promote a smaller obligation
   child;
4. keep the parent theorem from depending on equivalent support assumptions;
5. continue the normal counters: 15 build attempts or 15 review attempts before
   hard failure is legitimate.

Closed child obligations should remain in the ledger as history. If a
decomposition is superseded, mark the old child as superseded/closed through the
ledger mechanism rather than erasing it.

## Suggested Debt Batches

When no narrower user scope is given, preserve the historical next-batch order:

- Chapter 11 estimates and small interfaces first:
  `prob_11_4.density_mean_interface`,
  `prob_11_5.tail_summability_support`,
  `prob_11_6.sixth_moment_support`,
  `prob_11_6.tail_summability_support`,
  `prob_11_7.variance_decay_support`,
  `prob_11_8.covariance_decay_support`,
  `prob_11_9.occupancy_moment_calculation`,
  `prob_11_10.continuous_grid_uniformization`,
  `thm_11_7.fourth_moment_expansion_tail_bound`, then the small local
  interface debt `prob_14_6.obligation_2`.
- Then measure-theoretic extension and Fubini/pi-lambda work:
  `ex_13_5_1.rectangle_area`, `ex_13_5_1.pi_lambda_extension`,
  `thm_13_14.interval_fubini_calculation`, and
  `thm_13_14.pi_lambda_extension`.

These are ordering hints, not completion authority. Each task still requires
fresh build, semantic review, and apply evidence.

## Verification

For a focused task:

```powershell
lake env lean ToyApollo/Output/<task_id>.lean
python tools/validate_phase2_obligation_contracts.py --task <task_id>
python tools/validate_phase2_completion_classification.py --require-proof-contract
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

Do not edit `project_ledger.json` by hand during cleanup.
