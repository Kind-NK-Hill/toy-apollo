# Package Guide

Scope: everything under `src/toy_apollo/`.

## Purpose

This is the active package namespace behind `run_chapter.py`.

## Local Ownership

- `cli/`: argument parsing and phase dispatch
- `core/`: settings and ledger exports
- `integrations/`: reserved for future adapters; no active provider adapter is currently required
- phase helper modules at package root: prompt-pack and soft-dependency workflows

## Edit Rules

- Keep CLI flags and phase meanings stable unless the task explicitly calls for a contract change.
- If you change path behavior, check `src/toy_apollo/core/settings.py`.
- If you change phase behavior, align docs in `.claude/rules/10-phase-runtime.md`.

## Verify

- `python run_chapter.py -h`
- `python run_chapter.py --status`
