# Dependency Decision Trail

## Purpose

`project_ledger.json` records the current state of each task.  It tells us
which hard dependencies and soft imports are currently active.

The dependency decision trail records why an import was chosen.  It is an audit
log, not a replacement for the ledger.

## Storage

Decision records are stored as JSONL:

```text
dependency_decisions/<task_id>.jsonl
```

Each line is independent and idempotent by `decision_id`.

## Record Shape

```json
{
  "schema_version": 1,
  "decision_id": "thm_9_1|thm_7_12|hard|phase1_apply|explicit_text_reference",
  "recorded_at": "2026-05-10T00:00:00+00:00",
  "task_id": "thm_9_1",
  "dep_id": "thm_7_12",
  "kind": "hard",
  "phase": "phase1_apply",
  "criterion": "explicit_text_reference",
  "evidence": "Theorem 7.12",
  "source_plan": "chapter9-moments-mgf",
  "source_file": "plans/chapter9-moments-mgf_plan.json"
}
```

## Kinds

- `hard`: selected as a true task dependency.
- `soft`: selected as a problem-support import.
- `bridge`: selected to connect a textbook interface to a Mathlib interface.
- `materialized`: legacy audit kind for old external offload manifests; not emitted by the current CLI.
- `violation`: observed as an undeclared candidate import.
- `legacy_inferred`: inferred from old artifacts without changing them.

## Criteria

- `operator_declared_reliance`: already present in `draft_plan.json`.
- `explicit_text_reference`: injected from text such as `Theorem 7.12`.
- `soft_minimal_sufficient`: chosen by Phase 3 soft dependency selection.
- `interface_bridge`: needed to connect textbook and Mathlib formulations.
- `final_union_materialized`: legacy criterion for an old offload dependency manifest.
- `undeclared_candidate_import`: candidate imported something outside the
  declared hard/soft union.
- `legacy_inferred_from_output`: read-only inference from archived output.

## Phase Responsibilities

- Phase 1 records hard dependencies from operator declarations and explicit
  textbook references.
- Phase 1 plans are source-unit scoped.  A source unit is one numbered
  subsection, optionally with chapter intro for the first subsection, or one
  Problems section.  Do not use a whole-chapter plan as dependency authority.
- Phase 3 `soft-apply` records problem soft imports.
- Phase 2 consumes the final import union and writes
  `dependency_decision_context.*` into each prompt pack.
- Phase 2 `build-check` records undeclared local imports as violations.
- The current CLI does not materialize external offload manifests. Old `materialized` records, if present, are legacy audit data.

## History Policy

Archives and old prompt packs are read-only.  They may be inspected by
`tools/audit_dependency_history.py`, but the tool prints a report only.  It does
not write decision records and does not rewrite historical files.
