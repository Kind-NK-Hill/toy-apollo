# Phase 2 Batch Controller

This runbook defines the controller artifact for Phase 0-2 remaining-chapter
runs. It does not replace the Phase 2 entrypoint skill or the prompt-pack
workflow. It gives the current agent, a resumed agent, or a later agent a
durable checklist that can be checked without rerunning theorem work.

Use this controller when the scope contains more than one task. Phase 2 runtime
modes such as `pack`, `build-check`, `review-now`, `review-fix`, `debt-fix`,
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
- `COMPLETED`: task landed through the required workflow with no accepted proof debt.
- `COMPLETED_WITH_PROOF_DEBT`: task landed through the required workflow, but accepted explicit proof-debt support remains.
- `FAILED_LOCAL`: root hard-stopped task. Record `stop_reason`.
- `DEPENDENCY_FAILED`: downstream task skipped because a hard dependency failed
  inside this batch.
- `DEPENDENCY_PROOF_DEBT`: downstream task skipped because a direct or
  transitive hard dependency still has accepted proof debt.
- `MECHANISM_BLOCKER`: external or local mechanism prevents canonical progress,
  such as missing reviewer config or repeated timeout without a canonical result.
- `NEEDS_DECOMPOSITION`: complex proof task still has only the generated
  `source_proof_spine` placeholder or otherwise lacks concrete proof-obligation
  nodes. This is nonterminal and must not propagate dependency-failed skips.
- `USER_INTERRUPTED`: the user explicitly stopped or paused the batch.

A batch is terminal only when every task in scope has one of:
`COMPLETED`, `COMPLETED_WITH_PROOF_DEBT`, `FAILED_LOCAL`,
`DEPENDENCY_FAILED`, `DEPENDENCY_PROOF_DEBT`, `MECHANISM_BLOCKER`, or
`USER_INTERRUPTED`.

## Dependency-Failed Rule

If a root task reaches `FAILED_LOCAL` with stop reason `hard_failure`,
`nonprogress`, `max_rounds`, or `build_budget_exhausted`, mark every direct or
transitive uncompleted hard dependent in the current batch as
`DEPENDENCY_FAILED`.

For `hard_failure`, this propagation is allowed only after the failed root has
exhausted one Phase 2 failure streak counter: `phase2_build_fail_counter >= 15`
or `phase2_review_fail_counter >= 15`. A root that says `FAILED_LOCAL` before
either counter reaches 15 must be normalized back to `NONTERMINAL` by the
controller and must not block downstream tasks.

Do not apply this propagation when the root task's `proof_obligation_summary`
sets `needs_concrete_decomposition=true`; that state is `NEEDS_DECOMPOSITION`,
not a failed root.

Do not stop the batch after this propagation. Continue every remaining
independent `NONTERMINAL` task whose hard dependencies have not failed.

## Proof-Debt Dependency Rule

`COMPLETED_WITH_PROOF_DEBT` is terminal for the debt-bearing task itself, but it
is not a clean dependency. Every uncompleted direct or transitive hard dependent
must be marked `DEPENDENCY_PROOF_DEBT` and skipped until the blocker is repaired
through `debt-fix -> review-fix -> build-check -> review-now -> review-apply`.

The same rule applies to legacy tasks whose ledger status is still `COMPLETED`
but whose `proof_obligation_summary.status_counts.accepted_as_proof_debt` is
positive. The controller must normalize those rows to
`COMPLETED_WITH_PROOF_DEBT` for reporting and downstream blocking.

Accepted debt can also be promoted into first-class ledger children with
`--phase 2 --phase2-mode promote-obligations`. Each child has type
`Phase2ObligationTask`, records `parent_task_id`, `obligation_id`, and
`target_task_id`, and is processed by the same Phase2 loop as any other task.
The child owns its own attempt history and 15-attempt build/review failure
streaks; the parent remains the official output owner. Completed children stay
in the ledger as closed historical subtasks so later decomposition changes can
supersede them without losing audit history.

The batch summary must distinguish:

- `COMPLETED` tasks
- `COMPLETED_WITH_PROOF_DEBT` tasks
- root `FAILED_LOCAL` tasks grouped by `stop_reason`
- `DEPENDENCY_FAILED` tasks grouped by failed hard dependency
- `DEPENDENCY_PROOF_DEBT` tasks grouped by proof-debt hard dependency
- `MECHANISM_BLOCKER` tasks
- `USER_INTERRUPTED` tasks
- any remaining `NONTERMINAL` tasks

## Complex Retry Budget

For a complex task retried after an under-evidenced hard stop, a renewed attempt
must not be stopped again as `hard_failure` until either it completes or one of
these counters reaches 15:

- `phase2_build_fail_counter`: consecutive failed `build-check` attempts before
  semantic review. Failed build-check increments it; successful build-check
  resets it to `0`.
- `phase2_review_fail_counter`: failed or inconclusive semantic reviews of
  build-ready candidates. Failed/inconclusive review increments it; semantic
  pass completes the task.

Do not add build failures and review failures together. A task reaches
`FAILED_LOCAL` only when `phase2_build_fail_counter >= 15` or
`phase2_review_fail_counter >= 15`.

Record the live counters in each batch task:

```json
{
  "task_id": "thm_10_8",
  "status": "NONTERMINAL",
  "phase2_build_fail_counter": 0,
  "phase2_review_fail_counter": 3
}
```

Missing reviewer configuration, stale review refresh, dependency-failed skip,
setup failure, timeout, or manual abort without a canonical result file does not
increment either counter.

## Pre-Final Guard

Before a controller agent ends the turn or reports the batch as finished:

1. Run the status helper against the batch JSON.
2. Confirm every row is terminal.
3. Confirm every `DEPENDENCY_FAILED` row names a failed hard dependency.
4. Confirm every `DEPENDENCY_PROOF_DEBT` row names a proof-debt hard dependency.
5. Confirm every `hard_failure` has either `phase2_build_fail_counter >= 15` or
   `phase2_review_fail_counter >= 15`.
6. Confirm no `current_auto_loop_status = active` task lacks a documented stop
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
- `debt-fix` creates a single-task repair request for accepted proof debt; it is
  the repair path for proof-debt blockers.
- The batch status helper computes dependency-failed propagation, terminal
  coverage, proof-debt dependency blocking, and the two Phase 2 failure streak
  counters from the batch JSON.
- Phase 2 prompt-pack, build-check, review, auto-loop, and soft-dependency
  entrypoints refuse downstream work that would consume a hard or selected soft
  dependency carrying accepted proof debt.

Checklist-enforced today:

- Choosing the next independent task in deterministic batch order.
- Recording why a task is a root `FAILED_LOCAL` instead of ordinary repair work.
- Deciding that a mechanism blocker is terminal for the current user goal.
- Maintaining the batch JSON after each single-task Phase 2 operation.
- Ensuring the helper output is checked before a final batch summary.
