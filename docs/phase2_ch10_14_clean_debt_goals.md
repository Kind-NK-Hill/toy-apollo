# Chapter 10-14 Clean Debt Goals

This is the execution queue created after the stricter 2026-05-21 audit.
It covers every official output task in Chapter 10-14, not only theorem tasks.

The audit source of truth is:

```powershell
python .\tools\audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

Current report:

- `docs/phase2_ch10_14_clean_debt_surface_audit.md`
- `docs/phase2_ch10_14_clean_debt_surface_audit.json`

After the 2026-05-21 audit-tool correction and `prob_11_5` sample repair, the
strict report has 14 error tasks. `prob_11_5` remains visible only as review
surface because it proves a support package and keeps the support-consuming
helper internal.

## Completion Rule

A task is clean only when:

1. the relevant Lean file builds;
2. public task-facing declarations have no non-exception `Support`/`Spine`
   proof package parameter;
3. `proof_debt_support/status=proved` lands on theorem-level evidence, not a
   structure field, support predicate, or blank landing;
4. the normal Phase2 build/review/apply loop is fresh;
5. the strict audit no longer reports an `error` for that task.

The only standing exception is `thm_14_8_ProofBeyondBook`, including direct
downstream uses that explicitly inherit Theorem 14.8's beyond-book dependency.

## Goal A: Chapter 10 Quantile Surface

- `thm_10_8`

Remove the public `SkorokhodQuantileSupport` parameter by constructing the
remaining probability-measure and quantile event evidence internally, or by
adding theorem-level helper lemmas whose hypotheses match the textbook
statement.

## Goal B: Chapter 11 Estimate And Moment Tasks

- `prob_11_6`
- `prob_11_7`
- `prob_11_8`
- `prob_11_9`
- `prob_11_10`
- `thm_11_7`

Replace tail, moment, covariance, occupancy, and uniformization support
packages with theorem-level estimates. Each repaired task must remove public
support parameters and record real Lean landings in `proof_obligations.json`.

## Goal C: Chapter 13 Conditional Expectation/Fubini Tasks

- `thm_13_12`
- `thm_13_13`
- `thm_13_14`
- `ex_13_5_1`

Turn atom-integral, rectangle-area, Fubini, and pi-lambda extension support
objects into proved helper lemmas or shared local foundations. The final
task-facing declarations should expose the textbook conditional-expectation
claims, not a requirement to supply the proof support.

## Goal D: Chapter 14 Non-Beyond-Book Support Packages

- `prob_14_5`
- `prob_14_6`
- `thm_14_5`
- `thm_14_6`

Use the `thm_9_5` pattern: prove the source-step fields as lemmas, assemble any
spine internally, then remove the spine/support parameter from the public
declaration. For `thm_14_6`, review `def_14_3_IntervalMathlibTightBridge`
separately as an interface bridge; it is not automatically debt.

## Goal E: Beyond-Book Exception Hygiene

- `thm_14_8`
- `ex_14_4_3` inherited use
- `prob_14_11` inherited use

Keep `thm_14_8_ProofBeyondBook` visible as the only exception. Do not mark it
as ordinary proved proof debt. Downstream tasks may depend on it only when the
dependency is explicitly recorded as inherited beyond-book support.

## Operating Discipline

For each task:

1. inspect the official output and the current pack;
2. search existing `ToyApollo/Output` and Mathlib before writing new support;
3. write or import theorem-level evidence;
4. remove non-exception support/spine parameters from the public surface;
5. run the Lean file directly;
6. run Phase2 `build-check`;
7. run fresh semantic review and apply only a fresh pass;
8. rerun `audit_phase2_clean_debt_surface.py --fail-on-errors` for the task
   group before marking the goal complete.
