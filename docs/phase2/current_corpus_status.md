# Phase2 Current Corpus Status

This file is an index, not a generated report. Current status artifacts remain
at their tool-owned paths.

## Classification

- `docs/phase2_completion_classification.json`
- `docs/phase2_completion_classification.md`

Validate with:

```powershell
python tools/validate_phase2_completion_classification.py --require-proof-contract
```

## Clean Debt Surface

- `docs/phase2_ch10_14_clean_debt_surface_audit.json`
- `docs/phase2_ch10_14_clean_debt_surface_audit.md`

Regenerate with:

```powershell
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

## Unfinished Task Audit

- `docs/phase2_unfinished_tasks_audit.json`
- `docs/phase2_unfinished_tasks_audit.md`

These files are generated or maintained artifacts. Keep them at root `docs/`
unless the tools that read/write them are updated.

## Historical Step Reports

Reports under `docs/modification_0525_steps/` are historical execution records
and legacy compatibility paths. New stable Phase2 reports should go under
`docs/phase2/reports/`. Current policy is under `docs/phase2/`.
