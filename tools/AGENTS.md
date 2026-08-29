# Tools Guide

Scope: everything under `tools/`.

## Purpose

Scripts in this folder support hygiene, migration, reconciliation, and batch workflows.

## Edit Rules

- Keep scripts explicit and recoverable.
- Prefer guardrails over silent mutation.
- If a script changes repository structure or runtime state, document the expected inputs and outputs in comments or a runbook.

## Important Scripts

- `check_repo_hygiene.py`: tracked-artifact guard, not a full workspace cleanliness checker
- `sync_artifacts.ps1`: mirrors artifact paths between repos
- reconciliation and regression scripts: use only when the task explicitly calls for state repair
