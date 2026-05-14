# Tests Guide

Scope: everything under `tests/`.

## Purpose

Tests here mainly cover helper utilities and operator-driven workflow modules.

## Edit Rules

- Keep tests isolated from live runtime artifacts.
- Use temporary directories created inside the test case and clean them up.
- Avoid relying on repository-global `project_ledger.json` or output folders.

## Verify

- Run the narrowest relevant test module first.
- If a test needs filesystem fixtures, keep them disposable and local to the test.
