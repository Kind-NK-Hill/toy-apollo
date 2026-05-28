# Phase2 Problem Soft Dependency Workflow

Problem soft dependency selection is a Phase2 special case. It does not call an
external provider and does not prove Lean facts by itself.

## Commands

```powershell
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks <task_ids>
python .\run_chapter.py --phase 2 --phase2-mode soft-apply --tasks <task_ids> --selection .\selection.json
```

## Meaning

`soft-pack` prepares dependency-selection materials. The operator writes the
selection JSON. `soft-apply` records selected soft imports and marks the choice
confirmed.

An empty soft-import list must still be explicitly confirmed.
Having `candidate_snapshot.soft_imports` alone is not enough;
`soft_imports_confirmed_at` is the confirmation marker.

`soft-pack` and `soft-apply` accept only `Problem` task ids, and the selected
batch must stay within one chapter.

The selection JSON must have exactly the problem ids in the batch as keys. Each
value is an ordered list of selected soft imports.

## Boundary

Soft dependency selection:

- does not generate proof candidates;
- does not call a remote provider;
- does not replace Lean build checks;
- does not override proof-fidelity classification;
- must not consume `COMPLETED_WITH_PROOF_DEBT` as a clean dependency.

Do not under-select direct supporting theorems for closure or measurability
problems. Do not include the whole chapter by default.
