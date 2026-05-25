# Phase2 Step 5 Textbook-Complete Target Selection And Decision Freeze

Created: 2026-05-24
Status: completed Step 5 decision-freeze document

## Frozen Decision Result

Step 5 is now frozen by these companion records:

- `docs/modification_0525_steps/phase2_step5_textbook_complete_decision_record.md`
- `docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json`
- `docs/modification_0525_steps/phase2_step6_textbook_complete_proof_work_queue.md`

The frozen result is intentionally conservative:

- `prob_10_6`, `thm_11_7`, and `thm_13_14` are selected for the first Step 6
  Textbook Complete proof-work queue.
- `prob_10_5`, `prob_11_6`, and `prob_11_9` are not sent into proof
  implementation under their current statements; they remain explicit open debt
  until a statement or route rewrite is separately accepted.
- `thm_14_5` is resolved as an accepted Mathlib-backed adapter for the current
  pass. It is not counted as both an adapter and a Textbook Complete target.
- `thm_14_8_ProofBeyondBook` remains the unique root beyond-book exception, with
  only inherited downstream uses recorded.

No Lean proof file or `project_ledger.json` is edited by Step 5.

## Purpose

Step 5 is a decision-freeze step, not a Lean implementation step.

The goal is to decide which Good Corpus tasks should be upgraded toward
Textbook Complete, which tasks should remain Mathlib-backed adapters, and which
tasks should stay as explicit open debt or decision-needed work.

Step 5 must not:

- edit Lean proof files;
- mark any task as textbook complete merely because it builds;
- hide private axioms behind public support, bridge, or spine parameters;
- update `project_ledger.json`;
- start proof implementation before the target decisions are frozen.

Step 5 may:

- update this decision record;
- optionally create a machine-readable companion file later, such as
  `docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json`;
- prepare a proof-work queue for a later Step 6.

## Inputs

Read these files before making Step 5 decisions:

- `docs/modification_0525_steps/phase2_step4_good_corpus_final_report.md`
- `docs/modification_0525_steps/phase2_step4_good_corpus_family_work_queue.md`
- `docs/phase2_completion_classification.md`
- `docs/phase2_completion_classification.json`
- `docs/modification_0525_steps/phase2_interface_bridge_inventory.md`
- `docs/modification_0525_steps/phase2_textbook_fidelity_rework_evidence.md`

Step 4 currently reports Good Corpus status, not Textbook Complete status.
Remaining gaps are intentionally visible as `open_math_debt`,
`needs_decision`, `mathlib_backed_adapter_completed`, and the single
`beyond_book_exception`.

The Step 4 final report also records that the cleanup ran on an already dirty
local baseline and no checkpoint commit was created. Before any Step 6 proof
implementation, make a checkpoint commit or explicitly record that proof work is
continuing from a dirty baseline.

## Proposal Inspection Result

The proposed Step 5 shape is accepted with two refinements:

1. `thm_14_5` must be treated as a forked decision. It can either remain an
   accepted Mathlib-backed adapter, or it can become a Textbook Complete upgrade
   target. It must not be counted in both categories without an explicit
   decision.
2. Step 5 can be recorded as Markdown first. A JSON companion is useful for
   tooling, but it should not be required before the target decisions are stable.

## Step 5.0: Freeze The Step 4 Baseline

Before proof implementation:

- checkpoint the current Good Corpus state if the user authorizes a commit; or
- record the exact dirty baseline in the next proof-work report.

Required baseline checks:

```powershell
git status --short --untracked-files=all
python -m json.tool docs/phase2_completion_classification.json > $null
python tools/validate_phase2_completion_classification.py
python -m unittest tests.test_phase2_completion_classification
python -m py_compile tools/audit_phase2_clean_debt_surface.py
python -m unittest tests.test_phase2_clean_debt_surface_audit
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

Do not treat a clean audit as Textbook Complete evidence. Audit only checks the
public debt surface and metadata hygiene.

## Step 5.1: First-Priority Decision Gate

These four tasks cannot move directly into proof implementation because the
statement, bridge, or source model route is not frozen.

| priority | task_id | current_class | target_class after decision | blocker_declaration | allowed_route | decision_required | acceptance_criterion |
| ---: | --- | --- | --- | --- | --- | --- | --- |
| 1 | `prob_10_6` | `needs_decision` | `textbook_proof_completed` or `open_math_debt` | `prob_10_6_singleton_masses_to_distribution_internal` | Build an arbitrary countable-space singleton-mass to bounded-test/distribution bridge, or choose a finite-truncation/countable-integral route. | Decide whether the project wants a reusable countable-space bridge or will keep this reverse direction as open debt. | Private axiom removed and replaced by theorem-level bridge evidence; public theorem remains free of `Bridge`/`Support` proof-package parameters; Lean file builds. |
| 2 | `prob_10_5` | `needs_decision` | `textbook_proof_completed`, `mathlib_backed_adapter_completed`, or `open_math_debt` | `prob_10_5_dominated_probability_to_mean_internal` | Add a Vitali/subsequence-DCT bridge, rewrite to an a.e.-convergence DCT interface, or keep the current convergence-in-probability statement with explicit open debt. | Decide whether to strengthen/rewrite the statement or prove a new bridge matching the current textbook-facing statement. | No hidden measurability/uniform-integrability assumptions; any new hypothesis is recorded as a statement decision; private axiom removed only if theorem-level route exists. |
| 3 | `prob_11_6` | `needs_decision` | `textbook_proof_completed` or `open_math_debt` | `prob_11_6_sixthMomentSupport_internal` | Build reusable independent finite-sum sixth-moment expansion plus explicit measurability, integrability, a.e. bound, and mixed-term cancellation landings. | Decide whether to strengthen the random-variable interface with `AEStronglyMeasurable`/`MemLp`/a.e. bound hypotheses or prove the current statement as written. | Sixth-moment support is theorem-level evidence, not a private axiom; no fake `proved` metadata; final theorem public interface remains clean. |
| 4 | `prob_11_9` | `needs_decision` | `textbook_proof_completed` or `open_math_debt` | `prob_11_9_occupancy_moment_calculation_internal` | Rewrite around an explicit finite independent uniform balls-in-boxes model, or keep the abstract `X` interface and prove the moment calculation from stated hypotheses. | Decide whether the theorem statement should expose the concrete occupancy model needed for reuse from Chapter 6. | Empty-box first and second moment calculations land on theorem-level lemmas; any use of Chapter 6 occupancy results is actual theorem reuse, not name-only reuse. |

Do not start the larger Textbook Complete queue until these four decisions are
recorded as accepted routes, rejected routes, or intentionally open debt.

## Step 5.2: Candidate Textbook Complete Upgrade Targets

These are the core targets if the project wants to move beyond Good Corpus.
They should be considered in this order after Step 5.1 decisions are frozen.

| priority | task_id | current_class | target_class | blocker_declaration | allowed_route | decision_required | acceptance_criterion |
| ---: | --- | --- | --- | --- | --- | --- | --- |
| 1 | `thm_11_7` | `open_math_debt` | `textbook_proof_completed` | `thm_11_7_tail_summability_internal` | Formalize the fourth-moment expansion and tail-summability estimate at theorem level, reusing proved Chapter 11 estimate lemmas where they actually match. | No route decision needed unless the statement is found too weak for the estimate. | Private axiom removed; fourth-moment/tail lemma has a real theorem landing; `thm_11_7` builds and public interface stays clean. |
| 2 | `thm_13_14` | `open_math_debt` | `textbook_proof_completed` | `thm_13_14_conditional_expectation_internal` | Formalize interval Fubini, marginal/conditional density calculation, and pi-lambda or generator-extension route as theorem-level lemmas. | Decide only if the current density hypotheses are insufficient and need a statement change. | Private axiom removed; Fubini/pi-lambda obligations land on lemmas, not structure fields; final theorem builds. |
| 3 | `thm_14_7` | `open_math_debt` | `textbook_proof_completed` | `thm_14_7_quadratic_characteristic_expansion_internal` | Formalize centering, independent-sum characteristic convergence, quadratic expansion, and normal characteristic identification at theorem level. | Decide whether `thm_14_7_LindebergLevySetup` is acceptable source data or must be decomposed into theorem-level source lemmas. | Private axiom removed; setup fields used as source assumptions are clearly separated from proof fields; final theorem builds. |
| 4 | `thm_14_5` | `mathlib_backed_adapter_completed` | `textbook_proof_completed` only if selected | `thm_14_5_SourceProofSpine` | Reassemble the theorem through `thm_14_5_of_uniformTailBound` and theorem-level source-spine lemmas instead of relying mainly on the Mathlib-backed tightness adapter. | Explicitly decide whether this theorem must be upgraded or may remain an accepted adapter. | If upgraded, source-spine obligations land on theorem-level lemmas and adapter status is removed. If not upgraded, adapter classification remains explicit. |
| 5 | `thm_9_5` | reference/control pattern | control pattern, not default repair target | `CharacteristicInversionSourceSpine` | Use as the reference for internal spine construction and public theorem cleanliness. | Only review if the user requests strict proof-fidelity audit of Chapter 9. | Public theorem remains clean; no new repair work is opened unless evidence shows source-route fidelity problems. |

## Step 5.3: Accepted Adapter Set

These tasks may remain completed as adapters unless the user explicitly chooses
to upgrade them to Textbook Complete proof routes.

| task_id | current_class | allowed_status | reason | acceptance_criterion |
| --- | --- | --- | --- | --- |
| `thm_14_5` | `mathlib_backed_adapter_completed` | accepted adapter unless upgraded by Step 5.2 | Public theorem builds through Mathlib characteristic-function tightness and a local bridge; source spine remains open. | Classification continues to say adapter; source-spine route is not marked as textbook proof completed. |
| `thm_14_6` | `mathlib_backed_adapter_completed` | accepted adapter | Main theorem uses Mathlib tightness compactness/Prokhorov-style route and theorem-level interval bridge evidence. | No public `hbridge`; adapter classification remains explicit. |
| `prob_14_12` | `mathlib_backed_adapter_completed` | accepted adapter | Mean route is Mathlib-backed/interface evidence rather than strict source proof route. | Adapter classification remains explicit; no promotion to textbook complete without source-route rework. |
| `thm_14_1` | read-only adapter surface | accepted adapter surface | Anchors Ch14 characteristic-function/weak-convergence adapter material. | Keep as read-only bridge/adapter evidence unless promoted into classification later. |
| `thm_14_2` | read-only bridge surface | accepted bridge surface | Anchors distribution-to-weak bridge material used by Ch14 and Ch10 reasoning. | Keep bridge status explicit; do not count as proof of unrelated source obligations. |

## Step 5.4: Open Debt Backlog Not Prioritized For First Textbook Complete Pass

These tasks should remain explicit backlog unless the user reprioritizes them.
They should not block the first Textbook Complete target selection.

| task_id | current_class | blocker or boundary | recommended_status | acceptance_criterion |
| --- | --- | --- | --- | --- |
| `prob_11_8` | `open_math_debt` | AR(1) covariance-decay private axiom | keep open debt | Debt stays visible; no fake theorem landing. |
| `prob_11_10` | `open_math_debt` | continuous-grid uniformization private axiom | keep open debt | Debt stays visible; no fake theorem landing. |
| `prob_14_1` | `open_math_debt` | Polya/Stirling setup debt | keep open debt | Source setup and proof debt remain separated. |
| `prob_14_2` | `open_math_debt` | Gamma Lindeberg-Levy setup debt | keep open debt | Private axiom remains classified until theorem-level setup route exists. |
| `prob_14_8` | `open_math_debt` | MGF-to-characteristic convergence private axiom | keep open debt | Debt remains explicit. |
| `prob_14_10` | `open_math_debt` | bounded moments-to-MGF setup private axiom | keep open debt | Debt remains explicit. |
| `prob_14_11` | `open_math_debt` with inherited exception | coupon triangular array debt plus inherited `thm_14_8_ProofBeyondBook` | keep open debt plus inherited exception | Non-beyond-book private debts are separate from inherited beyond-book use. |
| `ex_14_4_1` | `open_math_debt` | Bernoulli Lindeberg-Levy setup private axiom | keep open debt | Debt remains explicit. |
| `ex_14_4_2` | `open_math_debt` | Poisson Lindeberg-Levy setup private axiom | keep open debt | Debt remains explicit. |
| `ex_14_4_3` | `open_math_debt` with inherited exception | Lyapunov verification private axiom plus inherited `thm_14_8_ProofBeyondBook` | keep open debt plus inherited exception | Lyapunov debt is not confused with the beyond-book exception. |

## Decision Record Schema

If a JSON companion is created later, each row should include at least:

```text
task_id
current_class
target_class
priority
blocker_declaration
allowed_route
decision_required
acceptance_criterion
decision_status
decision_owner
validation_commands
```

Allowed `decision_status` values:

- `pending`
- `accepted_for_textbook_complete`
- `accepted_as_adapter`
- `kept_as_open_debt`
- `needs_statement_rewrite`
- `rejected_for_current_scope`

## Step 5 Completion Criteria

Step 5 is complete when:

- all four Step 5.1 decision-gate tasks have a recorded route decision;
- each Step 5.2 candidate is either selected for Textbook Complete proof work or
  explicitly deferred;
- the accepted adapter set is frozen;
- the open debt backlog is frozen;
- the beyond-book boundary remains unique to `thm_14_8_ProofBeyondBook`, with
  only inherited usage recorded downstream;
- no Lean proof implementation is mixed into the decision-freeze commit.

Step 5 is not complete if:

- a `needs_decision` task is moved into proof work without a route decision;
- a Mathlib-backed adapter is silently promoted to Textbook Complete;
- a private axiom is treated as a proved source route;
- checkpoint status is unclear before proof implementation begins.

## Recommended Next Step After Step 5

After Step 5 is frozen, Step 6 should be a scoped proof-work batch. The first
reasonable Step 6 target is whichever Step 5.1 decision is accepted as a bridge
or statement route, with `prob_10_6` and `prob_10_5` being the most reusable
interface candidates, and `thm_11_7` / `thm_13_14` being the strongest core
theorem candidates.
