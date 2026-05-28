# Docs Guide

Scope: everything under `docs/`.

## Purpose

Use this folder for current runbooks and stable operator-facing policy docs.

## Edit Rules

- Keep root `AGENTS.md` and `CLAUDE.md` short; put detail here or in `.claude/rules/`.
- Match docs to current runtime behavior, not planned behavior.
- If Phase 4 is disabled in code, say so plainly.
- Prefer one topic per file over one giant overview document.
- Follow `docs/README.md` for the current runtime and policy boundary.
- Keep proof-fidelity, adapter, proof-debt, and public Support/Spine rules in
  `phase2/proof_fidelity_contract.md`; avoid re-expanding those rules in every
  workflow or handoff doc.
- Prefer git history, PR descriptions, or issues for historical one-off notes instead of adding them back under `docs/`.

## Avoid

- Duplicating the full root contract here
- Reintroducing deleted reorg/provider/handoff notes as current policy without checking code
