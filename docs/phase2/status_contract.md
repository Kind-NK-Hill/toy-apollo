# Phase2 Status Contract

`phase2_status` is the task-level Phase2 status. It is the only clean landing
guard.

Allowed values:

- `pass`
- `fail`
- `blocked`
- `allowed_exception`

The older `phase2_task_status` field may exist for compatibility, but new code
and reports should prefer `phase2_status`.

## Report-Only Statuses

Batch/status reports may derive additional display states from missing or stale
evidence. Reports must show these under a derived `report_status` or repair-hint
field, not under canonical `phase2_status`:

- `needs_fresh_review`
- `needs_class_normalization`

These are report-only repair hints. They are not canonical `phase2_status`
values and must not be written or interpreted as clean completion.

## Projection Inputs

The apply gate projects:

- semantic review verdict;
- reviewer `proof_class` / `completion_class`;
- source task role.

`proof_obligations.json` is a checklist and review context. It is not a status.
Ledger state, audit reports, classification files, batch state, validation
tools, and verify reports are not status authorities.

## Pass Rules

Proof-bearing tasks include theorem, problem, exercise, example, and internal
Phase2 obligation-child tasks. They pass only with source-route proof classes
such as:

- `textbook_proof_completed`
- `textbook_problem_completed`
- `textbook_exercise_completed`
- `source_route_proof_completed`
- `source_faithful_proof_completed`

Definition/interface tasks may pass with:

- `textbook_definition_completed`
- `definition_only_completed`
- `source_faithful_definition_bridge_completed`
- `source_faithful_notation_bridge_completed`
- `interface_bridge_completed`

`interface_bridge_completed` passes only for definition/interface/bridge roles.
It does not pass a theorem/problem/exercise task.

## Fail Rules

These proof classes or markers are fail/blocker evidence for local completion:

- `mathlib_backed_adapter_completed`
- `adapter`
- `open_math_debt`
- `proof_debt`
- `statement_weakened`
- `public_premise`
- `private_axiom`
- `semantic_fail`
- missing `proof_class` on a pass review

They may be useful evidence or repair targets, but they are not clean
completion.

## Blocked Rules

Dependency-gate markers such as `dependency_blocked`,
`dependency_failed`, and `fresh_review_refused_by_dependency_gate` project to
`blocked` unless the same class also contains local open-debt/adapter evidence,
which remains `fail`.

## Allowed Exception

`allowed_exception` is reserved for the explicit `thm_14_8` beyond-book
exception. It must not be generalized silently.
