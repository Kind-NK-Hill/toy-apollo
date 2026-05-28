# thm_13_14 Phase2 Repair Report: Pi-Lambda Bridge

Date: 2026-05-26

Task: `thm_13_14`

Mode: existing-output repair / Level 2 repair

## Result

`foundation_lemma_landed`.

The π-λ/generator extension step is now theorem-level Lean. Public `hExtend`
was removed from `thm_13_14` and `thm_13_14_identity`.

`thm_13_14` is not `textbook_proof_completed` yet. The interval Fubini
calculation remains a public `hIntervals` premise, and candidate-kernel
integrability is visible as `hKernelInt` rather than derived from the density
route.

## Lean Declarations

- `phase2_vectorMeasure_ext_of_Icc`
  - file: `ToyApollo/Phase2/VectorMeasureBorelBridge.lean`
  - reusable public bridge: equality of real-valued vector measures on all
    closed intervals implies equality on all Borel sets.
- `thm_13_14_verticalCylinder_measurable`
- `thm_13_14_closedIntervalCylinder_measurable`
- `thm_13_14_piLambdaExtensionSupport_from_integrable`
  - file: `ToyApollo/Output/thm_13_14.lean`
  - task-local use of the reusable bridge for the y-coordinate cylinder
    identity.

## Public Surface

Removed:

- public `hExtend` premise from `thm_13_14`
- public `hExtend` premise from `thm_13_14_identity`

Still present:

- public `hIntervals` premise
- public `hKernelInt` / identity-kernel integrability premise

These remaining assumptions are visible and keep the classification at
`open_math_debt`.

## Metadata

Updated:

- `phase2_prompt_packs/thm_13_14/proof_obligations.json`
- `docs/phase2_completion_classification.json`
- `docs/phase2_completion_classification.md`

The `pi_lambda_extension` obligation is marked proved with verified contract
evidence. The `interval_fubini_calculation` and final assembly remain open or
partial as appropriate.

## Validation

Commands run during this repair:

- `lake env lean ToyApollo/Phase2/VectorMeasureBorelBridge.lean`
- `lake env lean ToyApollo/Output/thm_13_14.lean`
- `python tools/validate_phase2_obligation_contracts.py --task thm_13_14`
- `python tools/validate_phase2_completion_classification.py --require-proof-contract`
- `python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors`
- `python -m unittest tests.test_phase2_completion_classification tests.test_phase2_clean_debt_surface_audit tests.test_phase2_obligation_contracts`

All commands above exited successfully in this repair batch. The clean-debt
surface audit reported `error_task_count: 0`. The unit-test command ran 27
tests and reported `OK`.
