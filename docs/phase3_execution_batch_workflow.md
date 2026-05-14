# Phase3 Execution Batch Workflow

> Historical/provider workflow. Current active Phase 3 runtime supports only
> `soft-pack` and `soft-apply`; do not treat the modes below as active CLI
> entrypoints unless the provider path is restored in code.

## Purpose

This document is the operator runbook for the second and third stages of `phase3`:

1. generate execution batches after soft selection has been confirmed
2. offload those batches to Aristotle in the planned order

This workflow exists because `soft selection` and `execution batching` are different problems:

- soft selection decides chapter-local supporting imports
- execution batching decides Aristotle scheduling order

## Preconditions

Before running execution-batch planning, every target `Problem` must already have:

- `candidate_snapshot.soft_imports`
- `soft_imports_confirmed_at`

That confirmation may represent either:

- a non-empty soft import list
- an explicitly confirmed empty list

## CLI Modes

```powershell
python .\run_chapter.py --phase 3 --phase3-mode plan-batches --tasks <problem_ids>
python .\run_chapter.py --phase 3 --phase3-mode offload-batch --batch <batch_id>
```

Rules:

- `plan-batches` only accepts `Problem` task ids
- `plan-batches` requires all selected tasks to belong to the same chapter
- `offload-batch` only accepts a batch id produced by a prior `plan-batches` run
- `offload-batch` does not rerun soft selection
- `offload-batch` refuses unconfirmed problem tasks instead of guessing soft imports

## Directory Layout

Each planning scope gets a directory:

- `phase3_execution_batches/<scope_id>/`

Typical contents:

- `batch_plan.json`
- `batch_plan.md`

Each concrete batch id is embedded in the plan, for example:

- `ch4_batch1__batch_1`
- `ch4_batch1__batch_2`

## Procedure

### Step 1: Generate the execution batch plan

```powershell
python .\run_chapter.py --phase 3 --phase3-mode plan-batches --tasks prob_4_2,prob_4_4,prob_4_8
```

Expected result:

- a new `phase3_execution_batches/<scope_id>/` directory appears
- `batch_plan.json` records the machine-readable batch structure
- `batch_plan.md` explains why each task is ready or blocked

### Step 2: Inspect the plan

Read:

1. `batch_plan.md`
2. `batch_plan.json`

Focus on:

- which tasks are in `batch_1`, `batch_2`, ...
- whether any tasks are marked `unscheduled`
- whether `missing completed deps` are due to unfinished imports
- whether `blocked by` lists show real problem-to-problem dependencies

### Step 3: Offload a single execution batch

```powershell
python .\run_chapter.py --phase 3 --phase3-mode offload-batch --batch <batch_id>
```

Example:

```powershell
python .\run_chapter.py --phase 3 --phase3-mode offload-batch --batch ch4_batch1__batch_1
```

What this does:

1. loads the planned batch from `phase3_execution_batches/`
2. resolves the exact problem ids for that batch
3. packages each task using:
   - hard dependencies
   - confirmed soft imports
   - final import union
4. sends them to Aristotle using the normal offload path

For the target Lean file, Phase 3 writes only a minimal `sorry` skeleton and includes the original problem statement plus dependency manifest context. It does not run a separate signature-extraction model call.

## Interpretation Rules

### `blocked by`

This field only refers to unresolved problem-to-problem dependencies inside the selected execution scope.

### `missing completed deps`

This field refers to required imports that are not yet `COMPLETED` in the ledger. These are not candidates for the current Aristotle batch.

### Same-batch placement

If many tasks are placed in `batch_1`, that means the current dependency graph does not force a stricter order. It is not a hardcoded semantic grouping.

## What This Workflow Does Not Do

- it does not perform soft selection
- it does not verify Lean locally
- it does not restore the disabled `phase4`
- it does not infer missing plan dependencies that are absent from the plan/ledger graph
