---
name: toy-apollo-phase2-entrypoint
description: Use when starting, resuming, reviewing, or repairing ToyApollo Phase 2 proof tasks, chapter batches, semantic review loops, hard-failure decisions, or complex Lean formalization work in this repository.
---

# ToyApollo Phase 2 Entrypoint

## Purpose

Use this skill as a thin entry router. It does not replace repository docs or repeat their full rules. It forces the agent to load the right source-of-truth documents before touching Lean files, ledgers, prompt packs, or review state.

## Required Reading

Read these files before doing task-specific work:

1. `AGENTS.md`
2. `docs/phase2_proof_fidelity_contract.md`
3. `docs/phase2_candidate_guidelines.md`
4. `docs/phase2_prompt_pack_workflow.md`
5. `docs/phase2_review_loop_protocol.md`

Read the task-local artifacts next:

1. `plans/<chapter>/<task>.json` or the relevant plan entry
2. `inputs/<source>.tex` for the original textbook statement and proof
3. Existing `ToyApollo/Output/*.lean` dependencies and `project_ledger.json`
4. Existing `phase2_prompt_packs/...` review, build, and obligation artifacts

## Start Checklist

Before editing, state the following in working notes:

1. Task id or chapter batch.
2. Whether the task is proof-bearing.
3. Original TeX source span inspected.
4. Existing local dependencies found in `ToyApollo/Output`.
5. Whether the task is normal or complex under the repository's structural criteria.
6. Current proof-fidelity target: textbook proof, Mathlib-backed adapter, interface bridge, open debt repair, or beyond-book exception.
7. Current ledger state and latest valid operation.
8. Intended route: authoring, build repair, semantic review repair, dependency skip, or hard-failure assessment.

## Complex Task Gate

Treat complexity as a structural property, not a theorem-name whitelist. Use
`docs/phase2_proof_fidelity_contract.md` for the Level 0/1/2 distinction,
complex decomposition rule, adapter/proof-debt boundary, and public
Support/Spine surface rule.

## Operation Route

Use the repository workflow rather than ad hoc state changes:

1. Generate or inspect the Phase 2 prompt pack.
2. Read the source grounding and dependency evidence from the pack, but verify against original TeX when the proof matters.
3. Edit candidate Lean.
4. Run local build checks.
5. Run semantic review on the candidate.
6. Apply only through `review-apply` when review passes.

Use `audit` or `verify` only when the reviewer runner is configured. If the runner is missing, treat that as a mechanism problem, not a substantive mathematical failure.

## Red Flags

Stop and re-read the required docs when any of these occur:

- Claiming `hard_failure` before source proof-spine decomposition, dependency search, and retry-budget evidence.
- Adding scaffold hypotheses that state the task's main conclusion or hide source mathematics.
- Treating a Mathlib-backed adapter, bridge theorem, private axiom, support field, or clean ledger row as textbook proof completion.
- Treating prompt-pack summaries as a substitute for original TeX.
- Landing a task without `review-apply`.
- Mixing unrelated dirty files, old plan reviews, and new chapter source output in one change.
- Stopping a chapter batch after one failed task while independent tasks remain.

## Expected Output

When this skill is used, produce a short entry report before implementation:

```text
Phase 2 entry report:
- Task scope:
- Source TeX inspected:
- Local dependencies:
- Complexity:
- Proof-fidelity target:
- Ledger state:
- Route:
- Immediate next command/action:
```
