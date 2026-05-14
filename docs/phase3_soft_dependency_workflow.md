# Phase3 Soft Dependency Workflow

## Purpose

This document is the operator runbook for the first stage of `phase3`: batch soft-dependency selection on `Problem` tasks.

The goal is to select chapter-local `def/thm` materials once, persist them to the ledger, and then reuse the same results in:

- `phase 2` prompt-pack problem formalization
- future `phase 3` Aristotle packaging

This is an operator-driven workflow. The code only prepares md/json materials; the actual `soft_imports_selection.json` is intended to be produced by the local Codex/GPT-5.4 operator workflow.

## Core Rule

`soft imports` are externally selected, but once selected they are mandatory imports.
Phase 3 offload does not infer missing soft imports automatically. A `Problem` task must have `soft_imports_confirmed_at`, even when the confirmed selection is an empty list.
Having `candidate_snapshot.soft_imports` alone is not enough; confirmation is explicit.

Canonical storage remains:

- `project_ledger.json -> tasks[task_id].candidate_snapshot.soft_imports`
- `project_ledger.json -> tasks[task_id].soft_imports_confirmed_at`

## CLI Modes

```powershell
python .\run_chapter.py --phase 3 --phase3-mode soft-pack --tasks <problem_ids>
python .\run_chapter.py --phase 3 --phase3-mode soft-apply --tasks <problem_ids> --selection <path>
```

Rules:

- only `Problem` task ids are allowed
- a batch may contain multiple problems
- `soft-pack` does not call Aristotle
- `soft-apply` does not offload anything

## Directory Layout

Each batch gets a directory:

- `phase3_softdep_packs/<batch_id>/`

Typical contents:

- `batch.json`
- `operator_prompt.md`
- `problem_statements.md`
- `selection_hints.md`
- `chapter_materials.md`
- `allowed_material_ids.json`
- `selection_schema.json`
- `soft_imports_selection.json`
- `apply_report.md`

## Procedure

### Step 1: Generate the batch pack

```powershell
python .\run_chapter.py --phase 3 --phase3-mode soft-pack --tasks prob_4_2,prob_4_4
```

Expected result:

- the batch directory appears under `phase3_softdep_packs/`
- no Aristotle call is made
- no ledger soft imports are changed yet

### Step 2: Read the pack

Read in this order:

1. `problem_statements.md`
2. `selection_hints.md`
3. `chapter_materials.md`
4. `allowed_material_ids.json`
5. `selection_schema.json`
6. `operator_prompt.md`

### Step 3: Produce the selection JSON

Write a JSON file whose keys are exactly the problem ids in the batch and whose values are ordered lists of selected soft imports.

Selection target:

- choose a minimal but sufficient import set
- do not under-select direct supporting theorems for closure/measurability problems
- do not include the whole chapter by default

Example:

```json
{
  "prob_4_2": ["def_4_3_sup_inf"],
  "prob_4_4": ["def_4_4_complex_random_variable", "def_4_4_complex_operations"]
}
```

### Step 4: Apply the selection

```powershell
python .\run_chapter.py --phase 3 --phase3-mode soft-apply --tasks prob_4_2,prob_4_4 --selection .\selection.json
```

Expected result:

- `candidate_snapshot.soft_imports` is updated in the ledger for each problem
- `soft_imports_confirmed_at` is set in the ledger for each problem
- `soft_imports_selection.json` in the batch directory is updated
- `apply_report.md` records the applied values

### Step 5: Verify ledger state

After `soft-apply`, inspect:

- `project_ledger.json`
- `phase3_softdep_packs/<batch_id>/apply_report.md`

The next step is not immediate Aristotle offload. The correct order is:

1. `soft-pack`
2. operator/Codex writes the selection JSON
3. `soft-apply`
4. `plan-batches`
5. `offload-batch`

If you are also doing local prompt-pack formalization for a `Problem`, the next local step is:

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks <problem_id>
```

## What This Workflow Does Not Do

- it does not change the canonical storage location
- it does not run Aristotle
- it does not verify Lean code
- it does not formalize the problem itself
- it does not generate execution batches
