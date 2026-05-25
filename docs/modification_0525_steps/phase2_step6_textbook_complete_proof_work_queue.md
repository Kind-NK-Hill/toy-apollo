# Phase2 Step 6 Textbook Complete Proof Work Queue

Created: 2026-05-24
Status: Step 6B strict proof landed for `prob_10_6`; statement-boundary cleanup landed for `thm_11_7` and `thm_13_14`

## Purpose

This queue is the first proof-work batch after Step 5. It exists so Step 6 starts
from frozen decisions instead of re-opening the entire Good Corpus backlog.

Step 6 must not promote any task unless the private axiom is removed and replaced
by theorem-level Lean evidence matching the selected route.

Current execution result:

- `docs/modification_0525_steps/phase2_step6_source_route_extraction_results.md`
- The first batch has completed Step 6A route extraction.
- `prob_10_6` completed strict Step 6B and is promoted to `textbook_proof_completed`.
- `thm_11_7` and `thm_13_14` had their private axioms removed, but remain
  `open_math_debt` because the remaining source proof steps are explicit public
  premises rather than internally derived theorem evidence.

## Execution Conventions: Skills And Subagents

Use `docs/modification_0525_steps/phase2_step6_source_proof_route_extraction_plan.md` as the controlling
protocol for skills and subagents.

Subagent policy: bounded per-target delegation only; no scope expansion. Every
subagent handoff must preserve the frozen Step 5 decisions and the Step 6A/6B
gate order.

In short:

- Step 6A route extraction is read-only and should use source-route and
  Lean-interface scout subagents when work can be split by target.
- Step 6B Lean implementation starts only after a target is marked
  `ready_for_lean`.
- Implementation workers must receive disjoint write scopes.
- Spec and quality review subagents should review route notes or Lean changes
  before a target is reported complete.
- Every Step 6 report should record `skills_used` and `assigned_subagents`.

## Baseline Rule

The repository is already dirty from prior Step 1-5 work. No checkpoint commit was
created in Step 5.

Before editing Lean in Step 6, either:

- create an authorized checkpoint commit; or
- keep this dirty-baseline record in the Step 6 proof report and update it with a
  fresh `git status --short --untracked-files=all` snapshot.

Current dirty-baseline snapshot recorded by Step 5:

```text
 M ToyApollo/Output/ex_14_4_3.lean
 M ToyApollo/Output/prob_11_10.lean
 M ToyApollo/Output/prob_11_6.lean
 M ToyApollo/Output/prob_11_8.lean
 M ToyApollo/Output/prob_11_9.lean
 M ToyApollo/Output/thm_11_7.lean
 M ToyApollo/Output/thm_13_14.lean
 M docs/phase2_ch10_14_clean_debt_surface_audit.json
 M docs/phase2_ch10_14_clean_debt_surface_audit.md
 M phase2_prompt_packs/ex_14_4_3/proof_obligations.json
 M phase2_prompt_packs/prob_11_10/proof_obligations.json
 M phase2_prompt_packs/prob_11_6/proof_obligations.json
 M phase2_prompt_packs/prob_11_8/proof_obligations.json
 M phase2_prompt_packs/prob_11_9/proof_obligations.json
 M phase2_prompt_packs/thm_11_7/proof_obligations.json
 M phase2_prompt_packs/thm_13_14/proof_obligations.json
?? docs/modification_0525_steps/phase2_ch14_worker_d_classification.md
?? docs/phase2_completion_classification.json
?? docs/phase2_completion_classification.md
?? docs/modification_0525_steps/phase2_completion_classification_step2_implementation_plan.md
?? docs/modification_0525_steps/phase2_interface_bridge_inventory.md
?? docs/modification_0525_steps/phase2_post_ch9_textbook_fidelity_rework_implementation_plan.md
?? docs/modification_0525_steps/phase2_step2_5_step1_unfinished_wrapup_plan.md
?? docs/modification_0525_steps/phase2_step3_interface_bridge_inventory_implementation_plan.md
?? docs/modification_0525_steps/phase2_step4_good_corpus_family_work_queue.md
?? docs/modification_0525_steps/phase2_step4_good_corpus_final_report.md
?? docs/modification_0525_steps/phase2_step4_good_corpus_lean_repair_implementation_plan.md
?? docs/modification_0525_steps/phase2_step5_textbook_complete_decision_record.md
?? docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json
?? docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.md
?? docs/modification_0525_steps/phase2_step6_textbook_complete_proof_work_queue.md
?? docs/modification_0525_steps/phase2_textbook_fidelity_rework_evidence.md
?? tests/test_phase2_completion_classification.py
?? tools/validate_phase2_completion_classification.py
```

## Selected Targets

| priority | task_id | current_class | target_class | blocker_declaration | frozen route | acceptance criterion |
| ---: | --- | --- | --- | --- | --- | --- |
| 1 | `prob_10_6` | `textbook_proof_completed` | `textbook_proof_completed` | `prob_10_6_singleton_masses_to_distribution_internal` | Build a reusable countable-space singleton-mass to bounded-test distribution bridge. Prefer countable TV or finite-truncation/countable-integral evidence; use `tv_distance_core` and `prob_14_5` only as proof seeds. | Private axiom removed; public theorem remains free of bridge/support proof-package parameters; `lake env lean ToyApollo/Output/prob_10_6.lean` passes. |
| 2 | `thm_11_7` | `open_math_debt` | `open_math_debt` after boundary cleanup | removed former `thm_11_7_tail_summability_internal` | Formalize the fourth-moment expansion and tail-summability estimate at theorem level. | Private axiom removed; `thm_11_7_from_tailSummability` builds; strict completion still needs theorem-level derivation of the public tail-summability premise. |
| 3 | `thm_13_14` | `open_math_debt` | `open_math_debt` after boundary cleanup | removed former `thm_13_14_conditional_expectation_internal` | Formalize interval Fubini, marginal/conditional density calculation, and generator-extension evidence as theorem-level lemmas. | Private axiom removed; `thm_13_14_from_intervalFubini_piLambda` builds; strict completion still needs theorem-level derivation of the public Fubini and extension premises. |

## Step 6A Result

| task_id | Step 6A route result | current-pass disposition | next required decision |
| --- | --- | --- | --- |
| `prob_10_6` | Route is feasible under the frozen custom countable-space interface. | Step 6B landed; promoted to `textbook_proof_completed`. | No current Step 6B proof action remains. |
| `thm_11_7` | Source route is clear, but current statement is not strict-completion-ready. | Statement-boundary cleanup landed; remains `open_math_debt`. | Derive the tail-summability premise internally from fourth-moment expansion evidence, or run a larger statement/foundation pass for explicit `MemLp`/measurability prerequisites. |
| `thm_13_14` | Source route is clear, but current statement is not strict-completion-ready. | Statement-boundary cleanup landed; remains `open_math_debt`. | Derive the Fubini and extension premises internally from density regularity/kernel integrability/generator-extension evidence, or run a larger statement/foundation pass. |

## Explicit Non-Targets

| task_id | frozen status | Step 6 rule |
| --- | --- | --- |
| `prob_10_5` | `kept_as_open_debt` | Do not start proof work until a Vitali/DCT bridge or statement rewrite is accepted. |
| `prob_11_6` | `kept_as_open_debt` | Do not start proof work until a moment-interface route is accepted. |
| `prob_11_9` | `kept_as_open_debt` | Do not start proof work until a concrete occupancy-model route is accepted. |
| `thm_14_5` | `accepted_as_adapter` | Do not upgrade in this batch; adapter classification remains frozen. |
| `thm_14_7` | `kept_as_open_debt` | Defer quadratic characteristic-expansion work to a later Ch14-focused batch. |

## Required Step 6 Preflight

Run before any Lean proof edit:

```powershell
git status --short --untracked-files=all
python -m json.tool docs/phase2_completion_classification.json > $null
python -m json.tool docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json > $null
python tools/validate_phase2_completion_classification.py
python -m unittest tests.test_phase2_completion_classification
python -m unittest tests.test_phase2_clean_debt_surface_audit
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

## Validation Per Target

For each edited target, run the target Lean file and the global classification and
audit checks:

```powershell
lake env lean ToyApollo/Output/<target>.lean
python tools/validate_phase2_completion_classification.py
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

## Completion Rule

A Step 6 target is complete only when:

- the blocker private axiom is removed;
- every replacement obligation has a theorem-level Lean landing;
- `docs/phase2_completion_classification.json` and Markdown classification are
  updated consistently;
- the Step 5 selected target is not replaced by an unrelated proof shortcut;
- the target Lean check and global validation commands pass.
