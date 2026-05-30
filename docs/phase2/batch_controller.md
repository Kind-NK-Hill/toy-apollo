# Phase2 Batch Controller

Use this for chapter-wide or ordered task-set work.

## Default Batch Behavior

When the user asks to review or repair an existing chapter, section, or ordered
task set, treat it as a same-session batch unless they explicitly ask for
prepare-only behavior.

For existing outputs:

- use `review_subject=existing`;
- process tasks in deterministic `block_id` order;
- apply pass results through `review-apply`;
- route fail/inconclusive results through repair/build/review/apply;
- for failed existing-output review, record repair-required evidence and
  preserve official output by default; quarantine is explicit opt-in
  maintenance after downstream import checks;
- continue independent tasks when a hard-stopped task blocks only its
  dependents.

## Durable Goals

For long batches, use a Codex goal when available. The goal must include stop
conditions such as completed, hard failure, nonprogress, max rounds, build
budget exhausted, or explicit user interruption.

For multi-task chapter/section runs, also maintain a durable batch-state JSON
when the work is meant to be resumed or checked by another agent. The batch
state records task ids, dependencies, status, stop reason, and Phase2 build/review
failure counters. Batch state is a resume/report cache, not a proof-status
authority. Use ledger runtime status and official output existence only as
workflow/apply evidence; the latest valid semantic review verdict remains the
proof-status authority.

The same checklist may include Phase 0 ingestion or Phase 1 planning rows for a
remaining-chapter run. Mark those preparatory rows with the same status names.
Use `MECHANISM_BLOCKER` for missing source material, invalid draft input, or
other non-proof infrastructure stops. Reserve `DEPENDENCY_FAILED` for hard
formalization dependencies inside the listed batch unless the batch explicitly
models a preparatory row as a hard dependency.

Run:

```powershell
python .\tools\phase2_batch_status.py path\to\batch_state.json
```

before a final batch summary. The helper normalizes terminal coverage,
dependency-failed propagation, proof-debt dependency routing, and hard-failure
counter checks. The default objective is `textbook-complete`; use
`--objective diagnostic` only when the user explicitly asks for a status
inventory or prepare-only report.

The status helper reports three different gates:

- `all_reporting_terminal`: every row has a reportable pause/failure state.
- `all_terminal`: every row is terminal for the selected objective.
- `all_clean_or_allowed_exception`: every row is clean `COMPLETED` or the
  unique allowed beyond-book exception.

## Required Artifact

For resumable task-set work, maintain one batch JSON file for the current goal.
Minimum shape:

```json
{
  "schema_version": "toy_apollo.phase2_batch_controller.v1",
  "batch_id": "chapter5_remaining_phase0_2",
  "scope": "Phase 0-2 remaining formal tasks for Chapter 5",
  "tasks": [
    {
      "task_id": "def_5_example",
      "status": "NONTERMINAL",
      "dependencies": [],
      "stop_reason": "",
      "complex_retry_after_under_evidenced_hard_stop": false,
      "failure_events": []
    }
  ]
}
```

Record live counters when relevant:

- `phase2_build_fail_counter`
- `phase2_review_fail_counter`

Counter updates are gate-specific. A failed build-check increments only
`phase2_build_fail_counter`, and the next successful build resets the build
failure streak for the current repair path. A failed or inconclusive semantic
review increments only `phase2_review_fail_counter`, and a passing semantic
review plus successful apply completes the current review path rather than
carrying the review-failure streak forward.

Missing reviewer configuration, stale review refresh, dependency-failed skip,
setup failure, timeout, or manual abort without a canonical result file does not
increment either counter.

## Batch Status Meaning

- `NONTERMINAL`: keep working when no user interruption or mechanism blocker
  stops the session.
- `COMPLETED`: landed through the required workflow with no accepted proof debt.
- `COMPLETED_WITH_PROOF_DEBT`: visible unfinished proof work. It is reportable
  in diagnostic mode, but it is not terminal for textbook-complete repair
  unless it is the allowed `thm_14_8` beyond-book exception.
- `FAILED_LOCAL`: root hard-stopped task with a documented stop reason.
- `DEPENDENCY_FAILED`: skipped because a hard dependency failed.
- `DEPENDENCY_PROOF_DEBT`: blocked because a hard dependency still carries
  accepted proof debt. In textbook-complete mode this is unfinished work:
  repair the upstream debt root before treating the downstream task as done.
- `NEEDS_DECOMPOSITION`: complex task still lacks concrete source-step
  obligation nodes; this is nonterminal and should not propagate dependency
  failure.
- `MECHANISM_BLOCKER`: blocked by setup, source, reviewer config, timeout, or
  other mechanism issue rather than a mathematical proof failure.
- `USER_INTERRUPTED`: the user explicitly paused or stopped the batch.

A batch is terminal only when every task in scope is terminal for the selected
objective. Do not read diagnostic terminal coverage as textbook completion.
Do not hand-edit batch state or classification to declare completion without a
passing review/apply trail.

## Batch Summary And Pre-Final Guard

Batch summaries must distinguish terminal coverage from mathematical success.
Report at least:

- clean `COMPLETED` tasks;
- `COMPLETED_WITH_PROOF_DEBT` tasks;
- root `FAILED_LOCAL` tasks, grouped by stop reason;
- `DEPENDENCY_FAILED` tasks, grouped by failed dependency;
- `DEPENDENCY_PROOF_DEBT` tasks, grouped by debt-bearing dependency;
- `MECHANISM_BLOCKER` tasks;
- `USER_INTERRUPTED` tasks;
- any remaining `NONTERMINAL` tasks.

Before the final response, confirm that every task in scope is terminal and
that no task still has `current_auto_loop_status = active` without a documented
stop reason. For repair requests whose wording is "finish", "fix", "clean",
or "textbook complete", also require `all_clean_or_allowed_exception = true`.
Every `DEPENDENCY_FAILED` row must name the failed hard dependency, every
`DEPENDENCY_PROOF_DEBT` row must name the proof-debt hard dependency. Every
`hard_failure` root must have either `phase2_build_fail_counter >= 15` or
`phase2_review_fail_counter >= 15`.

## Dependency Stops

A hard-stopped task makes hard dependents dependency-failed for that batch.
Skip those blocked dependents and continue independent tasks.

`COMPLETED_WITH_PROOF_DEBT` is not a clean dependency. Downstream tasks remain
blocked until debt is repaired and reviewed cleanly, except for explicit
inherited beyond-book handling from the unique `thm_14_8` exception.

Accepted debt can be promoted into first-class ledger children with
`--phase 2 --phase2-mode promote-obligations`. Each child has type
`Phase2ObligationTask`, records `parent_task_id`, `obligation_id`, and
`target_task_id`, and is processed by the same Phase2 loop as any other task.
The child owns its own attempt history and failure streaks; the parent remains
the official output owner. Completed children stay in the ledger as closed
historical subtasks so later decomposition changes can supersede them without
losing audit history.

For `hard_failure`, dependency propagation is valid only after the root task has
proper hard-stop evidence. In normal proof repair, that means either
`phase2_build_fail_counter >= 15` or `phase2_review_fail_counter >= 15`.
Build and review failures do not add together. A premature `FAILED_LOCAL`
without one of those counters should be treated as nonterminal repair work, not
as a downstream blocker.
