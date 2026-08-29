# Docs Guide

Scope: everything under `docs/`.

## Purpose

Use this folder for current runbooks and stable operator-facing policy docs.

## Edit Rules

- Keep root `AGENTS.md` and `CLAUDE.md` short; put detail here or in `.claude/rules/`.
- Match docs to current runtime behavior, not planned behavior.
- Document only the phases accepted by the current CLI; keep historical provider/offload notes out of current runbooks.
- Prefer one topic per file over one giant overview document.
- Follow `docs/README.md` for the current runtime and policy boundary.
- Keep Phase2 proof-fidelity, adapter, proof-debt, public Support/Spine, and
  status rules in `phase2/status_contract.md`, `phase2/review_criteria.md`,
  and `phase2/artifacts.md`; avoid re-expanding those rules in every workflow
  or handoff doc.
- Prefer git history, PR descriptions, or issues for historical one-off notes instead of adding them back under `docs/`.

## Avoid

- Duplicating the full root contract here
- Reintroducing deleted reorg/provider/handoff notes as current policy without checking code
