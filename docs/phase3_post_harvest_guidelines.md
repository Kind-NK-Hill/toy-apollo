# Phase3 Post-Harvest Guidelines

> Historical/provider guidance. Current active Phase 3 runtime supports only
> `soft-pack` and `soft-apply`; use this only when auditing or manually
> reconstructing old Aristotle harvest work.

## Purpose

These are the candidate-writing rules for post-Aristotle local repair.

They are narrower than the workflow document. This file is about how to repair the Lean candidate itself.

## Core Principle

Repair the smallest thing that restores a valid local result.

Do not quietly change the task statement just because Aristotle did.

## Failure Classes

### `proof_incomplete`

Meaning:

- task statement still matches the staged package
- the local failure is in proof or implementation detail

Allowed action:

- repair the body

### `statement_drift`

Meaning:

- Aristotle changed the declaration header relative to the staged package

Allowed action:

- audit the statement
- reconcile textbook intent and Lean semantics

Not allowed:

- silently accepting the drifted statement as the original task

### `harvest_missing_clean_file`

Meaning:

- no clean raw file was harvested

Allowed action:

- audit the harvest
- consider re-offload or statement review

Not allowed:

- ordinary proof repair as if a stable baseline existed

## Hard Rules

1. No `sorry`.
2. No Markdown.
3. Do not edit dependency files.
4. For `proof_incomplete`, do not change the theorem or definition statement.
5. For `statement_drift`, do not pretend the raw statement is the original task.
6. Prefer local dependency reuse over restating previous chapter material.
7. Keep the repaired artifact useful to downstream tasks.

## Preferred Repair Order

1. preserve the original statement
2. reuse imported Mathlib objects
3. reuse imported `ToyApollo.Output.*` objects
4. replace brittle tactics with shorter robust proof steps
5. only then restructure a proof more substantially

## Aristotle Summary Usage

Read the summary, but do not treat it as ground truth.

Use it for:

- the model's intended proof route
- why it changed the statement, if it did
- candidate theorem names it relied on

Do not use it to justify:

- statement drift
- silent weakening or strengthening of hypotheses

## Verification Log Usage

Treat the local verification log as the primary failure evidence.

Use it to identify:

- unsolved goals
- unknown identifiers
- import failures
- theorem-header drift that caused build mismatch

## Limsup/Liminf Sequence Problems

For textbook sequence limsup/liminf problems:

- prefer chapter-local `seqLimsup` / `seqLiminf`
- prefer tail `sup` / `inf` formulations when equivalent
- avoid `Filter.limsup` on `ℝ` unless the problem is explicitly filter-theoretic

Reason:

- textbook limsup is an analysis object with extended-value semantics
- `Filter.limsup` on `ℝ` can force extra boundedness assumptions that are not in the original task

## Reference Cases

### `prob_4_8`

Interpretation:

- normal `proof_incomplete`
- statement is acceptable
- repair should target the proof body

### `prob_4_11`

Interpretation:

- canonical `statement_drift`
- Aristotle added boundedness because it interpreted the task using `Filter.limsup`
- repair should not continue on the drifted theorem without first reconciling statement semantics
