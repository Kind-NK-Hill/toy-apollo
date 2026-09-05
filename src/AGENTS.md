# Source Tree Guide

Scope: everything under `src/`.

## Purpose

- `src/formalization_engine/*` is the canonical package layout and owns the
  active runtime.

## Edit Rules

- Add new runtime code under `src/formalization_engine/*`.
- Do not add root-level compatibility modules under `src/`.
- Keep imports and behavior compatible with the stable CLI entry.

## Verify

- `python run_chapter.py -h`
- relevant unit tests under `tests/`
