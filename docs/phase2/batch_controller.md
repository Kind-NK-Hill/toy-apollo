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
- continue independent tasks when a hard-stopped task blocks only its
  dependents.

## Durable Goals

For long batches, use a Codex goal when available. The goal must include stop
conditions such as completed, hard failure, nonprogress, max rounds, build
budget exhausted, or explicit user interruption.

For multi-task chapter/section runs, also maintain a durable batch-state JSON
when the work is meant to be resumed or checked by another agent. The batch
state records task ids, dependencies, status, stop reason, and Phase2 build/review
failure counters. Use:

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

## Dependency Stops

A hard-stopped task makes hard dependents dependency-failed for that batch.
Skip those blocked dependents and continue independent tasks.

`COMPLETED_WITH_PROOF_DEBT` is not a clean dependency. Downstream tasks remain
blocked until debt is repaired and reviewed cleanly, except for explicit
inherited beyond-book handling from the unique `thm_14_8` exception.

For `hard_failure`, dependency propagation is valid only after the root task has
proper hard-stop evidence. In normal proof repair, that means either
`phase2_build_fail_counter >= 15` or `phase2_review_fail_counter >= 15`.
Build and review failures do not add together. A premature `FAILED_LOCAL`
without one of those counters should be treated as nonterminal repair work, not
as a downstream blocker.
