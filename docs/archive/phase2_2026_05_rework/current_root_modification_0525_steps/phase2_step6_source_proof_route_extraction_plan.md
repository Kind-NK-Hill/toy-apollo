# Phase2 Step 6 Source Route Extraction And Signature Freeze Protocol

Created: 2026-05-24
Rewritten: 2026-05-25
Status: historical first Step 6 plan rewritten to match the current Step 6-8 split

## Current Authority

The current Step 6 entry is:

- `docs/modification_0525_steps/phase2_step6_contract_gated_textbook_completion_plan.md`

This file keeps the detailed protocol for Step 6A/6B. It no longer authorizes
Lean proof implementation. Any older language saying that Step 6B edits Lean has
been superseded by the Step 7/8 split:

```text
Step 6A: source route extraction
Step 6B: expected theorem signature freeze
Step 7: bridge / foundation lemma completion
Step 8: scoped target Lean implementation
```

## Scope

Step 6 consumes the frozen decisions from:

- `docs/modification_0525_steps/phase2_step5_textbook_complete_decision_record.md`
- `docs/modification_0525_steps/phase2_step5_textbook_complete_target_selection.json`
- `docs/modification_0525_steps/phase2_step5_6_contract_reconciliation_report.md`

The first selected targets remain:

1. `prob_10_6`
2. `thm_11_7`
3. `thm_13_14`

Historical result:

- `prob_10_6` already landed theorem-level proof work and is locked as
  `textbook_proof_completed`.
- `thm_11_7` and `thm_13_14` remain open and must go through Step 7 before
  final target assembly can be attempted.

## Step 6A Output

For each selected target, Step 6A must record:

- original source locations inspected;
- current Lean file and declaration names inspected;
- current blocker declaration or public proof premise;
- source proof route, decomposed into named mathematical steps;
- public assumption expansion: local `def` / `structure` / package assumptions
  unfolded far enough to detect hidden strengthening;
- earlier ToyApollo theorem-level reuse opportunities;
- interface bridge candidates;
- Mathlib APIs that may be used locally;
- missing bridge / foundation lemmas;
- statement sufficiency status;
- destination: `locked_completed`, `ready_for_step7`, `ready_for_step8`,
  `needs_step5_statement_decision`, or `non_target`.

Step 6A is read-only with respect to Lean proof files.

## Step 6B Output

Step 6B freezes the handoff contract for the next productive step. It must
produce or update a route/signature note containing:

```text
task_id
selected_obligation_ids
expected_theorem_signatures
minimal_first_lemma
allowed_imports
allowed_local_reuse
allowed_mathlib_role
write_scope_for_step7
write_scope_for_step8
forbidden_shortcuts
validation_commands
handoff_destination
```

The most important field is `minimal_first_lemma`: Step 7 should be able to
start with one concrete theorem statement, not a broad prose blocker.

Step 6B may update route documents and `proof_obligations.json` contract fields
when it is freezing expected signatures. It must not edit `ToyApollo/Output/*.lean`
except to revert an accidental proof-production edit before reporting.

## Required Target Gates

Before freezing a target, run:

```powershell
python tools/validate_phase2_completion_classification.py --require-proof-contract
python tools/validate_phase2_obligation_contracts.py --task <task_id>
```

Do not require the global obligation-contract validator to pass. The global
backlog is tracked by Step 5.6 and is not a Step 6 proof route blocker.

## Current First-Batch Handoffs

Detailed historical route notes live in:

- `docs/modification_0525_steps/phase2_step6_source_route_extraction_results.md`

The current productive handoff is:

- `thm_11_7` -> Step 7, starting with the tail-summability-from-fourth-moment
  foundation route.
- `thm_13_14` -> Step 7, starting with interval-Fubini and generator-extension
  foundation routes.

`prob_10_6` is locked and should not be reopened unless a regression appears.

## Completion Criteria

Step 6 is complete for a target only when:

- its source route is decomposed;
- at least one expected theorem signature is frozen, or the target is sent back
  to Step 5 for a statement/route decision;
- the handoff destination is recorded;
- no Lean proof-production claim is made.

`open_math_debt` is not a terminal Step 6 outcome. It must be converted into a
Step 7 foundation queue item or a Step 5 decision item.
