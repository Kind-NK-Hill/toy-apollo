# Phase2 Problem Soft Dependency Workflow

Problem soft dependency selection is a Phase2 special case. It does not call an
external provider and does not prove Lean facts by itself.

## Commands

```powershell
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks <task_ids>
python .\run_chapter.py --phase 2 --phase2-mode soft-apply --tasks <task_ids> --selection .\selection.json
```

## Meaning

`soft-pack` prepares dependency-selection materials. This is an operator-driven
workflow: code prepares markdown/JSON materials, and the local operator writes
the selection JSON. `soft-apply` records selected soft imports and marks the
choice confirmed.

The goal is to select chapter-local definition and theorem material once,
persist it to the ledger, then reuse that selection in pack, build, and review.

An empty soft-import list must still be explicitly confirmed.
Having `candidate_snapshot.soft_imports` alone is not enough;
`soft_imports_confirmed_at` is the confirmation marker.

`soft-pack` and `soft-apply` accept only `Problem` task ids, and the selected
batch must stay within one chapter.

Canonical storage remains:

- `project_ledger.json -> tasks[task_id].candidate_snapshot.soft_imports`
- `project_ledger.json -> tasks[task_id].soft_imports_confirmed_at`

The selection JSON must have exactly the problem ids in the batch as keys. Each
value is an ordered list of selected soft imports.

## Directory Layout

Each batch gets `phase2_softdep_packs/<batch_id>/`.

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

1. Run `soft-pack`.
2. Read `problem_statements.md`, `selection_hints.md`,
   `chapter_materials.md`, `allowed_material_ids.json`, and
   `selection_schema.json`, then `operator_prompt.md`.
3. Write `soft_imports_selection.json`.
4. Run `soft-apply --selection <path>`.
5. Inspect `project_ledger.json` and
   `phase2_softdep_packs/<batch_id>/apply_report.md`.

The next step is not provider offload. Continue locally with Phase2 `pack`,
`build-check`, and `review-now`.

## Boundary

Soft dependency selection:

- does not generate proof candidates;
- does not call a remote provider;
- does not replace Lean build checks;
- does not override proof-fidelity classification;
- must not consume `COMPLETED_WITH_PROOF_DEBT` as a clean dependency.

Do not under-select direct supporting theorems for closure or measurability
problems. Do not include the whole chapter by default.
