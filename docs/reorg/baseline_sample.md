# Baseline Sample (Stage A)

- Date: 2026-03-30
- Branch: `reorg`
- Scope: Capture one chapter baseline for Phase 1/2 regression comparison.

## Selected Input

- Chapter source: `inputs/01_chap3_premeasure.tex`
- Plan output target: `plans/01_chap3_premeasure_plan.json`

## Intended Checks

1. Phase 1 output count in generated plan.
2. `project_ledger.json` state transitions after Phase 2.
3. Hashes of:
   - `reports/01_chap3_premeasure_report.md`
   - `formalized_chapters/01_chap3_premeasure_Formalized.lean`
   - `output_lean_files/**/*`

## Execution Status

- Executed on 2026-03-30 with command:
  - `python run_chapter.py --phase 1 --input .\inputs\01_chap3_premeasure.tex`
- Result: **Failed before parser execution** due missing credential:
  - `ValueError: No API key was provided. Please pass a valid API key.`
- Environment check (sandbox + elevated): `DEEPSEEK_API_KEY=EMPTY`.
- Phase 2 was not executed because Phase 1 plan generation did not complete.

This file remains the fixed acceptance checklist. Re-run baseline after setting:

```powershell
$env:DEEPSEEK_API_KEY = "<your-key>"
```
