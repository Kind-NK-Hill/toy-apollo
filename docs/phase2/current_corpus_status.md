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

The Chapter 10-14 clean-debt rule is: a task is clean only when the Lean file
builds, public task-facing declarations have no non-exception `Support`/`Spine`
proof-package parameter, proved proof-debt support lands on theorem-level
evidence, the normal build/review/apply loop is fresh, and the strict audit no
longer reports an error for that task.

The only standing beyond-book exception is `thm_14_8_ProofBeyondBook`,
including direct downstream uses that explicitly inherit Theorem 14.8's
beyond-book dependency.

Current stable goal groups:

- Chapter 10 quantile surface: remove the public `SkorokhodQuantileSupport`
  parameter from `thm_10_8` by constructing the remaining
  probability-measure and quantile event evidence internally, or by adding
  theorem-level helper lemmas whose hypotheses match the textbook statement.
- Chapter 11 estimates and moments: replace tail, moment, covariance,
  occupancy, and uniformization support packages with theorem-level estimates
  for `prob_11_6`, `prob_11_7`, `prob_11_8`, `prob_11_9`, `prob_11_10`, and
  `thm_11_7`.
- Chapter 13 conditional expectation/Fubini tasks: turn atom-integral,
  rectangle-area, Fubini, and pi-lambda extension support objects into proved
  helper lemmas or shared local foundations for `thm_13_12`, `thm_13_13`,
  `thm_13_14`, and `ex_13_5_1`.
- Chapter 14 non-beyond-book support packages: use the `thm_9_5` pattern to
  prove source-step fields as lemmas, assemble spines internally, and remove
  support parameters from public declarations for `prob_14_5`, `prob_14_6`,
  `thm_14_5`, and `thm_14_6`. For `thm_14_6`, review
  `def_14_3_IntervalMathlibTightBridge` separately as an interface bridge; it
  is not automatically debt.
- Beyond-book exception hygiene: keep `thm_14_8_ProofBeyondBook` visible as the
  only exception, and record inherited beyond-book support explicitly for
  `thm_14_8`, `ex_14_4_3`, and `prob_14_11`.

Known ledger hygiene: visible child rows
`obl_thm_14_4_triangle_density_bound` and
`obl_thm_14_4_adapted_theorem_8_6_identity` may remain visible even when parent
`thm_14_4` is `COMPLETED` and the obsolete obligations are already recorded at
the parent level. Treat those rows as ledger hygiene to reconcile, not active
mathematical proof debt by themselves.

For each task, inspect the official output and current pack, search
`ToyApollo/Output` and Mathlib before writing new support, write or import
theorem-level evidence, remove non-exception support/spine parameters, run the
Lean file directly, run Phase2 `build-check`, run fresh semantic review/apply,
and rerun the clean-debt audit before marking the goal complete.

## Unfinished Task Audit

- `docs/phase2_unfinished_tasks_audit.json`
- `docs/phase2_unfinished_tasks_audit.md`

These files are generated or maintained artifacts. Keep them at root `docs/`
unless the tools that read/write them are updated.

## Historical Step Reports

Reports under `docs/modification_0525_steps/` are historical execution records
and legacy compatibility paths. New stable Phase2 reports should go under
`docs/phase2/reports/`. Current policy is under `docs/phase2/`.
