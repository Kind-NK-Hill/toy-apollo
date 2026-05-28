# Phase2 Step 6 Route Freeze Work Queue

Created: 2026-05-24
Rewritten: 2026-05-25
Status: current Step 6 queue after the Step 6-8 split

## Purpose

This file used to be the Step 6 proof-work queue. It is now only the Step 6
route/signature-freeze queue.

Proof-production has moved to:

- Step 7: `docs/modification_0525_steps/phase2_step7_bridge_foundation_completion_plan.md`
- Step 8: `docs/modification_0525_steps/phase2_step8_scoped_lean_implementation_plan.md`

## Current Step 6 Queue

| priority | task_id | Step 6 status | handoff |
| ---: | --- | --- | --- |
| 1 | `prob_10_6` | locked completed from historical proof work | no action |
| 2 | `thm_11_7` | route extracted; expected tail-summability foundation route frozen | Step 7 |
| 3 | `thm_13_14` | route extracted; expected interval-Fubini / extension route frozen | Step 7 |
| 4 | `ex_14_4_3` | not selected in current Step 6 pass | future Step 6 route freeze if user selects local Lyapunov debt |
| 5 | `thm_14_5` | accepted adapter | no Step 6 upgrade unless Step 5 is reopened |

## Historical Execution Result

Historical details are recorded in:

- `docs/modification_0525_steps/phase2_step6_source_route_extraction_results.md`
- `docs/modification_0525_steps/phase2_step6_contract_gated_execution_report.md`

Important interpretation:

- `prob_10_6` is the successful proof-production example, but that work now
  belongs conceptually to the Step 7/8 pattern, not to future Step 6 work.
- `thm_11_7` and `thm_13_14` are not Step 6 failures. They are Step 7 inputs:
  Step 6 found the foundation lemmas that must be proved before final target
  assembly.
- `returned_to_open_math_debt` is not a terminal proof-production result.

## Step 6 Completion Rule

A current Step 6 queue item is complete when:

- route extraction exists;
- expected theorem signatures or first foundation lemma candidates are frozen;
- the target is handed to Step 7, Step 8, Step 5, or no action;
- no Lean proof-production claim is made.

Do not report Step 6 completion as "Lean proof done" unless the target was
already historically locked before this rewrite.

## Non-Targets

| task_id | reason |
| --- | --- |
| `prob_10_5` | Step 5 kept it open until a Vitali/DCT bridge or statement rewrite is accepted. |
| `prob_11_6` | Step 5 kept it open until a moment-interface route is accepted. |
| `prob_11_9` | Step 5 kept it open until a concrete occupancy-model route is accepted. |
| `thm_14_7` | Deferred; needs its own Step 6 route/signature freeze before Step 7. |

The remaining Step 5.6 global contract queues are not part of this Step 6 queue
unless a specific task is selected and passed through target-level contract
gating.
