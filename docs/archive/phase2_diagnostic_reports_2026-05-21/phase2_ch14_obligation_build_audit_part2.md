# Phase2 Unfinished Task Audit

- Generated at: `2026-05-22T00:34:52.642756Z`
- Scope: chapters `9`-`14`
- Extra included tasks: `thm_6_7__lemma_1`
- Task filter: `prob_14_11, thm_14_7, thm_14_8`
- Bucket filter: `(none)`
- Build checked: `True`
- Build timeout seconds: `240`
- Unfinished or verify count: `3`
- Blocking unfinished count: `3`
- Verification-only count: `0`
- Orphan output count: `10`

## Reason Counts

- `completed_with_proof_debt`: 1
- `ledger_status:COMPLETED_WITH_PROOF_DEBT`: 1
- `ledger_status:FAILED_LOCAL`: 2
- `open_obligations`: 2

## Open Obligation Kinds

- `proof_debt_support`: 6
- `interface-name matches`: 0
- `structure-field landings`: 5
- `theorem wrappers over structure fields`: 0
- `empty landings`: 0
- `ledger-only child obligations`: 6

## Build Status Counts

- `ok`: 3

## Repair Batches

- `obligation_resolution` (2): `prob_14_11, thm_14_7`
  - action: Resolve the open proof obligations and land them on theorem/lemma declarations rather than structure fields.
- `allowed_beyond_book_hygiene` (1): `thm_14_8`
  - action: Keep only the documented thm_14_8 beyond-book exception and make inherited uses explicit.

## Tasks

- `prob_14_11` ch14 `FAILED_LOCAL` `ToyApollo/Output/prob_14_11.lean` `obligation_resolution`: `ledger_status:FAILED_LOCAL`, `open_obligations`
  - open: `obligation_2, obligation_3, obligation_4`
  - obligation `obligation_2` `proof_debt_support`: status `open`, landing `prob_14_11_CouponRatioTriangularArraySetup.theoremSetup / source_rows_are_independent / source_coupon_collection_law_is_stage_sum`, landing problem `structure_field_landing`, child `obl_prob_14_11_obligation_2` `FAILED_LOCAL` output `False`
  - obligation `obligation_3` `proof_debt_support`: status `open`, landing `prob_14_11_asymptoticMeanScale / prob_14_11_asymptoticVarianceScale / mean_asymptotic / variance_asymptotic`, landing problem `missing_theorem_or_lemma_landing`, child `obl_prob_14_11_obligation_3` `FAILED_LOCAL` output `False`
  - obligation `obligation_4` `proof_debt_support`: status `open`, landing `prob_14_11_CouponRatioTriangularArraySetup.generalized_lyapunov_condition`, landing problem `structure_field_landing`, child `obl_prob_14_11_obligation_4` `FAILED_LOCAL` output `False`
  - build: `ok`
- `thm_14_7` ch14 `FAILED_LOCAL` `ToyApollo/Output/thm_14_7.lean` `obligation_resolution`: `ledger_status:FAILED_LOCAL`, `open_obligations`
  - open: `center_and_standardize, quadratic_characteristic_expansion, independent_sum_characteristic`
  - obligation `center_and_standardize` `proof_debt_support`: status `open`, landing `thm_14_7_LindebergLevySetup.mean, thm_14_7_LindebergLevySetup.sigma, thm_14_7_LindebergLevySetup.standardizedLaws`, landing problem `structure_field_landing`, child `obl_thm_14_7_center_and_standardize` `FAILED_LOCAL` output `False`
  - obligation `quadratic_characteristic_expansion` `proof_debt_support`: status `open`, landing `thm_14_7_quadraticCharacteristicExpansion, thm_14_7_LindebergLevySetup.quadratic_expansion`, landing problem `structure_field_landing`, child `obl_thm_14_7_quadratic_characteristic_expansion` `FAILED_LOCAL` output `False`
  - obligation `independent_sum_characteristic` `proof_debt_support`: status `open`, landing `thm_14_7_LindebergLevySetup.c, thm_14_7_LindebergLevySetup.c_definition`, landing problem `structure_field_landing`, child `obl_thm_14_7_independent_sum_characteristic` `FAILED_LOCAL` output `False`
  - build: `ok`
- `thm_14_8` ch14 `COMPLETED_WITH_PROOF_DEBT` `ToyApollo/Output/thm_14_8.lean` `allowed_beyond_book_hygiene`: `ledger_status:COMPLETED_WITH_PROOF_DEBT`, `completed_with_proof_debt`
  - build: `ok`

## Orphan Output Files

- `thm_9_5_dirichlet` ch9 `ToyApollo/Output/thm_9_5_dirichlet.lean`: `missing_ledger_entry`
- `thm_9_5_fubini` ch9 `ToyApollo/Output/thm_9_5_fubini.lean`: `missing_ledger_entry`
- `thm_9_5_kernel` ch9 `ToyApollo/Output/thm_9_5_kernel.lean`: `missing_ledger_entry`
- `prob_10_10_distribution_bridge` ch10 `ToyApollo/Output/prob_10_10_distribution_bridge.lean`: `missing_ledger_entry`
- `thm_10_8_inverse_comparison` ch10 `ToyApollo/Output/thm_10_8_inverse_comparison.lean`: `missing_ledger_entry`
- `thm_10_8_quantile_convergence` ch10 `ToyApollo/Output/thm_10_8_quantile_convergence.lean`: `missing_ledger_entry`
- `thm_10_8_quantile_defs` ch10 `ToyApollo/Output/thm_10_8_quantile_defs.lean`: `missing_ledger_entry`
- `thm_10_8_quantile_law` ch10 `ToyApollo/Output/thm_10_8_quantile_law.lean`: `missing_ledger_entry`
- `thm_10_8_quantile_space` ch10 `ToyApollo/Output/thm_10_8_quantile_space.lean`: `missing_ledger_entry`
- `thm_14_4_dominating_measure` ch14 `ToyApollo/Output/thm_14_4_dominating_measure.lean`: `missing_ledger_entry`
