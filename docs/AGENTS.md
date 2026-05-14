# Docs Guide

Scope: everything under `docs/`.

## Purpose

Use this folder for runbooks, migration notes, and operator-facing workflow docs.

## Edit Rules

- Keep root `AGENTS.md` and `CLAUDE.md` short; put detail here or in `.claude/rules/`.
- Match docs to current runtime behavior, not planned behavior.
- If Phase 4 is disabled in code, say so plainly.
- Prefer one topic per file over one giant overview document.
- Follow `docs/README.md` for the active, historical, and archive boundary.
- Mark historical inspection notes clearly; do not let them read like current operator instructions.

## Avoid

- Duplicating the full root contract here
- Treating historical reorg notes as current policy without checking code
