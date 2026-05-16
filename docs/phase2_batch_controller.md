# Phase 2 Batch Controller

This runbook defines the controller artifact for Phase 0-2 remaining-chapter
runs. It does not replace the Phase 2 entrypoint skill or the prompt-pack
workflow. It gives the current agent, a resumed agent, or a later agent a
durable checklist that can be checked without rerunning theorem work.

Use this controller when the scope contains more than one task. Phase 2 runtime
modes such as `pack`, `build-check`, `review-now`, `review-fix`,
`auto-loop`, and `review-apply` remain single-task operations. The controller
therefore schedules and records task-set state; it does not run an unattended
theorem-proving daemon.

The same checklist can include Phase 0 ingestion and Phase 1 planning items for
a remaining-chapter run. Mark those preparatory items with the same status names
and use `MECHANISM_BLOCKER` for missing source material, invalid draft input, or
other non-proof infrastructure stops. `DEPENDENCY_FAILED` is reserved for hard
formalization dependencies inside the listed batch unless the batch explicitly
models a preparatory item as a hard dependency.

## Required Artifact

Create one batch JSON file for the current goal, for example:

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

Allowed controller statuses:

- `NONTERMINAL`: not terminal; the controller must keep working if no user
  interruption or mechanism blocker stops the session.
- `COMPLETED`: task landed through the required workflow.
- `FAILED_LOCAL`: root hard-stopped task. Record `stop_reason`.
- `DEPENDENCY_FAILED`: downstream task skipped because a hard dependency failed
  inside this batch.
- `MECHANISM_BLOCKER`: external or local mechanism prevents canonical progress,
  such as missing reviewer config or repeated timeout without a canonical result.
- `USER_INTERRUPTED`: the user explicitly stopped or paused the batch.

A batch is terminal only when every task in scope has one of:
`COMPLETED`, `FAILED_LOCAL`, `DEPENDENCY_FAILED`, `MECHANISM_BLOCKER`, or
`USER_INTERRUPTED`.

## Dependency-Failed Rule

If a root task reaches `FAILED_LOCAL` with stop reason `hard_failure`,
`nonprogress`, `max_rounds`, or `build_budget_exhausted`, mark every direct or
transitive uncompleted hard dependent in the current batch as
`DEPENDENCY_FAILED`.

Do not stop the batch after this propagation. Continue every remaining
independent `NONTERMINAL` task whose hard dependencies have not failed.

The batch summary must distinguish:

- `COMPLETED` tasks
- root `FAILED_LOCAL` tasks grouped by `stop_reason`
- `DEPENDENCY_FAILED` tasks grouped by failed hard dependency
- `MECHANISM_BLOCKER` tasks
- `USER_INTERRUPTED` tasks
- any remaining `NONTERMINAL` tasks

## Complex Retry Budget

For a complex task retried after an under-evidenced hard stop, a renewed attempt
must not be stopped again as `hard_failure` until either it completes or records
15 substantive failures.

Count only:

- `build_check_failure` after a meaningful candidate, decomposition, plan, or
  strategy change
- `semantic_review_fail` or `semantic_review_inconclusive` for a build-ready
  candidate
- `review_apply_rejection` caused by semantic or freshness evidence

Do not count:

- missing reviewer configuration
- stale refresh that only regenerates review material
- dependency-failed skip
- timeout or manual abort without a canonical result file
- setup failure
- repeated identical failure fingerprint without a changed candidate,
  decomposition plan, helper structure, or search strategy

Record counted and skipped attempts in `failure_events`:

```json
{
  "kind": "build_check_failure",
  "candidate_changed": true,
  "canonical_result": true,
  "failure_fingerprint": "unknown_identifier: foo",
  "candidate_hash": "sha256-or-short-id",
  "strategy_key": "rewrite-helper-chain-v2"
}
```

For `review_apply_rejection`, set `rejection_class` to `semantic` or
`freshness` when it should count.

## Pre-Final Guard

Before a controller agent ends the turn or reports the batch as finished:

1. Run the status helper against the batch JSON.
2. Confirm every row is terminal.
3. Confirm every `DEPENDENCY_FAILED` row names a failed hard dependency.
4. Confirm every complex retry hard failure has at least 15 substantive
   failures.
5. Confirm no `current_auto_loop_status = active` task lacks a documented stop
   reason in ledger metadata.

Helper command:

```powershell
python .\tools\phase2_batch_status.py path\to\batch_state.json
```

Use `--json` when another script or agent needs normalized output.

## Enforced Boundaries

Program-enforced today:

- Phase 2 core CLI modes are single-task, except `review-existing-queue` and
  Problem soft-dependency modes.
- `auto-loop` records live phase/status/stop fields in ledger runtime metadata
  and mirrors them into prompt-pack metadata.
- `review-apply` is the only Codex semantic-review landing step.
- The batch status helper computes dependency-failed propagation, terminal
  coverage, and conservative 15-failure budget counts from the batch JSON.

Checklist-enforced today:

- Choosing the next independent task in deterministic batch order.
- Recording why a task is a root `FAILED_LOCAL` instead of ordinary repair work.
- Deciding that a mechanism blocker is terminal for the current user goal.
- Maintaining the batch JSON after each single-task Phase 2 operation.
- Ensuring the helper output is checked before a final batch summary.
