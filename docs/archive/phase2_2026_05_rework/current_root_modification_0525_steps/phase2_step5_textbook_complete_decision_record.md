# Phase2 Step 5 Textbook Complete Decision Record

Created: 2026-05-24
Status: Step 5 decision freeze complete

## Scope

This record completes the Step 5 target-selection freeze described in
`docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.md`.

Step 5 does not edit Lean proof files, does not update `project_ledger.json`, and
does not promote any task to Textbook Complete merely because the Lean file builds.

The decisions below freeze which Good Corpus tasks are selected for the first
Step 6 proof-work batch, which tasks remain accepted adapters, and which tasks
stay as explicit open debt.

## Baseline

The Step 5 decision freeze was made on the already dirty Step 4 local baseline.
No checkpoint commit was created in this pass.

`project_ledger.json` was not edited.

The baseline checks required by the Step 5 plan are part of the final validation
section of this record. The exact dirty baseline for the next proof-work batch is
also copied into `docs/modification_0525_steps/phase2_step6_textbook_complete_proof_work_queue.md` so
Step 6 does not begin from an ambiguous state.

## Decision Policy

The freeze uses these rules:

- A private axiom remains open debt until replaced by theorem-level Lean evidence.
- A Mathlib-backed adapter remains an adapter unless a source-route proof is
  explicitly selected and later implemented.
- A public setup structure can be source data, but it is not proof-completion
  evidence by itself.
- A `needs_decision` task must receive a route decision before proof work starts.
- `thm_14_8_ProofBeyondBook` is the only root beyond-book exception.

## Step 5.1 Decision Gate

| priority | task_id | current_class | frozen_target | decision_status | route decision | Step 6 disposition |
| ---: | --- | --- | --- | --- | --- | --- |
| 1 | `prob_10_6` | `needs_decision` | `textbook_proof_completed` | `accepted_for_textbook_complete` | Build a theorem-level countable-space singleton-mass to bounded-test distribution bridge. Prefer a reusable countable TV or finite-truncation/countable-integral route, using `tv_distance_core` and `prob_14_5` only as seeds, not as current closure. | Selected as Step 6 priority 1. |
| 2 | `prob_10_5` | `needs_decision` | `open_math_debt` | `kept_as_open_debt` | Do not prove the current statement by adding hidden assumptions. A future pass must first choose between a Vitali/subsequence-DCT bridge and a statement rewrite to an a.e.-convergence DCT interface. | Deferred until statement/route rewrite is accepted. |
| 3 | `prob_11_6` | `needs_decision` | `open_math_debt` | `kept_as_open_debt` | Do not start proof work under the current random-variable interface. A future pass must first accept explicit `AEStronglyMeasurable`/`MemLp`/a.e. bound prerequisites or a reusable sixth-moment finite-sum layer. | Deferred until moment-interface route is accepted. |
| 4 | `prob_11_9` | `needs_decision` | `open_math_debt` | `kept_as_open_debt` | Do not prove the abstract `X` interface as if it were the concrete occupancy model. A future pass must rewrite around an explicit finite independent uniform balls-in-boxes model or keep the abstract moment calculation open. | Deferred until occupancy-model route is accepted. |

These four rows now have route decisions, so no Step 5.1 task is left without a
frozen decision status.

## Step 5.2 Textbook Complete Upgrade Targets

| priority | task_id | current_class | frozen_target | decision_status | route decision | Step 6 disposition |
| ---: | --- | --- | --- | --- | --- | --- |
| 1 | `thm_11_7` | `open_math_debt` | `textbook_proof_completed` | `accepted_for_textbook_complete` | Formalize the fourth-moment expansion and tail-summability estimate at theorem level. The private axiom `thm_11_7_tail_summability_internal` must be removed only after real theorem landings exist. | Selected as Step 6 priority 2. |
| 2 | `thm_13_14` | `open_math_debt` | `textbook_proof_completed` | `accepted_for_textbook_complete` | Formalize interval Fubini, marginal/conditional density calculation, and generator-extension evidence as theorem-level lemmas. | Selected as Step 6 priority 3. |
| 3 | `thm_14_7` | `open_math_debt` | `open_math_debt` | `rejected_for_current_scope` | Keep the quadratic characteristic expansion debt visible for this first pass. It should be decomposed later into centering, independent-sum characteristic convergence, quadratic expansion, and normal characteristic identification. | Deferred from first Step 6 batch. |
| 4 | `thm_14_5` | `mathlib_backed_adapter_completed` | `mathlib_backed_adapter_completed` | `accepted_as_adapter` | Resolve the fork by keeping `thm_14_5` as an accepted Mathlib-backed adapter in this pass. It is not selected for Textbook Complete upgrade unless a later pass explicitly chooses the source-spine route. | Frozen as adapter, not Step 6 proof target. |
| 5 | `thm_9_5` | reference/control pattern | control pattern | `rejected_for_current_scope` | Use as a pattern for internal source-spine construction and public theorem cleanliness. Do not open repair work without separate evidence. | Read-only control pattern. |

## Accepted Adapter Set

| task_id | frozen_status | reason |
| --- | --- | --- |
| `thm_14_5` | `accepted_as_adapter` | Fork resolved: current pass keeps the Mathlib characteristic-function tightness adapter and does not count the source spine as complete. |
| `thm_14_6` | `accepted_as_adapter` | Main route remains Mathlib-backed compactness/tightness with theorem-level interval bridge evidence. |
| `prob_14_12` | `accepted_as_adapter` | Mean route is Mathlib-backed/interface evidence rather than strict textbook source route. |
| `thm_14_1` | `accepted_as_adapter_surface` | Read-only Ch14 characteristic-function/weak-convergence adapter surface. |
| `thm_14_2` | `accepted_as_bridge_surface` | Read-only distribution-to-weak bridge surface used as supporting evidence only. |

## Open Debt Backlog

These tasks are frozen as explicit backlog for the first Textbook Complete pass.
They must not block Step 6 priority work and must not be silently promoted.

| task_id | frozen_status | boundary |
| --- | --- | --- |
| `prob_10_5` | `kept_as_open_debt` | Needs statement or Vitali/DCT route decision before proof work. |
| `prob_11_6` | `kept_as_open_debt` | Needs moment-interface route decision before proof work. |
| `prob_11_8` | `kept_as_open_debt` | AR(1) covariance-decay private axiom remains visible. |
| `prob_11_9` | `kept_as_open_debt` | Needs concrete occupancy-model route decision before proof work. |
| `prob_11_10` | `kept_as_open_debt` | Continuous-grid uniformization private axiom remains visible. |
| `prob_14_1` | `kept_as_open_debt` | Polya/Stirling setup debt remains visible. |
| `prob_14_2` | `kept_as_open_debt` | Gamma Lindeberg-Levy setup debt remains visible. |
| `prob_14_8` | `kept_as_open_debt` | MGF-to-characteristic convergence debt remains visible. |
| `prob_14_10` | `kept_as_open_debt` | Bounded moments-to-MGF setup debt remains visible. |
| `prob_14_11` | `kept_as_open_debt_with_inherited_exception` | Coupon triangular-array debt remains separate from inherited `thm_14_8_ProofBeyondBook` usage. |
| `ex_14_4_1` | `kept_as_open_debt` | Bernoulli Lindeberg-Levy setup debt remains visible. |
| `ex_14_4_2` | `kept_as_open_debt` | Poisson Lindeberg-Levy setup debt remains visible. |
| `ex_14_4_3` | `kept_as_open_debt_with_inherited_exception` | Lyapunov debt remains separate from inherited `thm_14_8_ProofBeyondBook` usage. |
| `thm_14_7` | `kept_as_open_debt` | Quadratic characteristic-expansion route is deferred from first Step 6 batch. |

## Beyond-Book Boundary

The root beyond-book boundary is frozen:

- `thm_14_8_ProofBeyondBook` is the only root beyond-book exception.
- `ex_14_4_3` and `prob_14_11` may record inherited usage only.
- No other private axiom or adapter may be reclassified as a beyond-book
  exception without a separate Step 5-style decision.

## Step 6 Queue

The first Step 6 proof-work batch is frozen as:

1. `prob_10_6`: countable singleton-mass to bounded-test distribution bridge.
2. `thm_11_7`: fourth-moment/tail-summability proof route.
3. `thm_13_14`: interval Fubini and conditional-density proof route.

The detailed queue is in
`docs/modification_0525_steps/phase2_step6_textbook_complete_proof_work_queue.md`.

## Completion Criteria Check

| criterion | result |
| --- | --- |
| All four Step 5.1 decision-gate tasks have route decisions. | passed |
| Each Step 5.2 candidate is selected or explicitly deferred. | passed |
| Accepted adapter set is frozen. | passed |
| Open debt backlog is frozen. | passed |
| Beyond-book boundary remains unique to `thm_14_8_ProofBeyondBook`. | passed |
| No Lean proof implementation is mixed into Step 5. | passed |

## Validation

Required validation commands:

```powershell
git status --short --untracked-files=all
python -m json.tool docs/phase2_completion_classification.json > $null
python tools/validate_phase2_completion_classification.py
python -m unittest tests.test_phase2_completion_classification
python -m py_compile tools/audit_phase2_clean_debt_surface.py
python -m unittest tests.test_phase2_clean_debt_surface_audit
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
python -m json.tool docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json > $null
```

Final validation result:

- `git status --short --untracked-files=all` recorded the existing dirty baseline
  plus the new Step 5 decision documents.
- `python -m json.tool docs/phase2_completion_classification.json > $null`
  passed.
- `python -m json.tool docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json
  > $null` passed.
- `python tools/validate_phase2_completion_classification.py` passed.
- `python -m unittest tests.test_phase2_completion_classification` passed.
- `python -m py_compile tools/audit_phase2_clean_debt_surface.py` passed.
- `python -m unittest tests.test_phase2_clean_debt_surface_audit` passed.
- `python tools/audit_phase2_clean_debt_surface.py --write-report
  --fail-on-errors` passed with `error_task_count: 0`.
