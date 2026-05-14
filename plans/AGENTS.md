# Plans Guide

Scope: everything under `plans/`.

## Purpose

Plan JSON files are generated task queues and fallback candidate sources for runtime workflows.

## Edit Rules

- Do not mass-edit plan files unless the task is explicitly about migration or reconciliation.
- Preserve `block_id`, `type`, `title`, `content`, and `dependencies` shape.
- `offload_candidates_legacy.json` is audit and backfill material, not the default source of truth.

## Caution

- Editing plans can desync them from `project_ledger.json`.
- Prefer fixing generators or reconciliation tools instead of hand-patching many plan files.
