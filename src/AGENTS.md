# Source Tree Guide

Scope: everything under `src/`.

## Purpose

- `src/*.py` still contains active compatibility-layer runtime logic.
- `src/toy_apollo/*` is the target package layout for future code ownership.

## Edit Rules

- Prefer adding new code under `src/toy_apollo/*`.
- Do not assume `src/*.py` is dead code; many package modules still rely on it.
- Keep imports and behavior compatible with the stable CLI entry.

## Verify

- `python run_chapter.py -h`
- relevant unit tests under `tests/`
