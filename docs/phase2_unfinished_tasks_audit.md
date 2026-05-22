# Phase2 Unfinished Task Audit

- Generated at: `2026-05-22T00:36:27.085156Z`
- Scope: chapters `9`-`14`
- Extra included tasks: `thm_6_7__lemma_1`
- Task filter: `(none)`
- Bucket filter: `(none)`
- Build checked: `False`
- Build timeout seconds: `120`
- Unfinished or verify count: `14`
- Blocking unfinished count: `13`
- Verification-only count: `1`
- Orphan output count: `10`

## Reason Counts

- `completed_with_proof_debt`: 1
- `critical_ch6_bridge_verify`: 1
- `ledger_status:COMPLETED_WITH_PROOF_DEBT`: 1
- `ledger_status:FAILED_LOCAL`: 12
- `open_obligations`: 12
- `public_surface_error`: 7

## Open Obligation Kinds

- `proof_debt_support`: 18
- `interface-name matches`: 0
- `structure-field landings`: 9
- `theorem wrappers over structure fields`: 3
- `empty landings`: 5
- `ledger-only child obligations`: 18

## Repair Batches

- `critical_bridge_verification` (1): `thm_6_7__lemma_1`
  - action: Build-check the Chapter 6 bridge and keep it in the report as a critical dependency, even though it is already completed.
- `public_surface_and_obligations` (7): `prob_11_10, prob_11_6, prob_11_8, prob_11_9, thm_11_7, thm_13_14, ex_14_4_3`
  - action: First remove public Support/Spine parameters, then close the named proof obligations with theorem-level landings.
- `obligation_resolution` (5): `prob_14_1, prob_14_10, prob_14_11, prob_14_8, thm_14_7`
  - action: Resolve the open proof obligations and land them on theorem/lemma declarations rather than structure fields.
- `allowed_beyond_book_hygiene` (1): `thm_14_8`
  - action: Keep only the documented thm_14_8 beyond-book exception and make inherited uses explicit.

## Tasks

- `thm_6_7__lemma_1` ch6 `COMPLETED` `ToyApollo/Output/thm_6_7__lemma_1.lean` `critical_bridge_verification`: `critical_ch6_bridge_verify`
- `prob_11_10` ch11 `FAILED_LOCAL` `ToyApollo/Output/prob_11_10.lean` `public_surface_and_obligations`: `ledger_status:FAILED_LOCAL`, `open_obligations`, `public_surface_error`
  - open: `continuous_grid_uniformization`
  - obligation `continuous_grid_uniformization` `proof_debt_support`: status `open`, landing `(none)`, landing problem `empty_landing`, child `obl_prob_11_10_continuous_grid_uniformization` `FAILED_LOCAL` output `False`
- `prob_11_6` ch11 `FAILED_LOCAL` `ToyApollo/Output/prob_11_6.lean` `public_surface_and_obligations`: `ledger_status:FAILED_LOCAL`, `open_obligations`, `public_surface_error`
  - open: `sixth_moment_support`
  - obligation `sixth_moment_support` `proof_debt_support`: status `open`, landing `(none)`, landing problem `empty_landing`, child `obl_prob_11_6_sixth_moment_support` `FAILED_LOCAL` output `False`
- `prob_11_8` ch11 `FAILED_LOCAL` `ToyApollo/Output/prob_11_8.lean` `public_surface_and_obligations`: `ledger_status:FAILED_LOCAL`, `open_obligations`, `public_surface_error`
  - open: `covariance_decay_support`
  - obligation `covariance_decay_support` `proof_debt_support`: status `open`, landing `(none)`, landing problem `empty_landing`, child `obl_prob_11_8_covariance_decay_support` `FAILED_LOCAL` output `False`
- `prob_11_9` ch11 `FAILED_LOCAL` `ToyApollo/Output/prob_11_9.lean` `public_surface_and_obligations`: `ledger_status:FAILED_LOCAL`, `open_obligations`, `public_surface_error`
  - open: `occupancy_moment_calculation`
  - obligation `occupancy_moment_calculation` `proof_debt_support`: status `open`, landing `(none)`, landing problem `empty_landing`, child `obl_prob_11_9_occupancy_moment_calculation` `FAILED_LOCAL` output `False`
- `thm_11_7` ch11 `FAILED_LOCAL` `ToyApollo/Output/thm_11_7.lean` `public_surface_and_obligations`: `ledger_status:FAILED_LOCAL`, `open_obligations`, `public_surface_error`
  - open: `fourth_moment_expansion_tail_bound`
  - obligation `fourth_moment_expansion_tail_bound` `proof_debt_support`: status `open`, landing `(none)`, landing problem `empty_landing`, child `obl_thm_11_7_fourth_moment_expansion_tail_bound` `FAILED_LOCAL` output `False`
- `thm_13_14` ch13 `FAILED_LOCAL` `ToyApollo/Output/thm_13_14.lean` `public_surface_and_obligations`: `ledger_status:FAILED_LOCAL`, `open_obligations`, `public_surface_error`
  - open: `interval_fubini_calculation, pi_lambda_extension`
  - obligation `interval_fubini_calculation` `proof_debt_support`: status `open`, landing `thm_13_14_closedIntervalCylinder_eq_prod`, child `obl_thm_13_14_interval_fubini_calculation` `FAILED_LOCAL` output `False`
  - obligation `pi_lambda_extension` `proof_debt_support`: status `open`, landing `thm_13_14_verticalCylinder_eq_prod`, child `obl_thm_13_14_pi_lambda_extension` `FAILED_LOCAL` output `False`
- `ex_14_4_3` ch14 `FAILED_LOCAL` `ToyApollo/Output/ex_14_4_3.lean` `public_surface_and_obligations`: `ledger_status:FAILED_LOCAL`, `open_obligations`, `public_surface_error`
  - open: `lyapunov_fourth_moment_bound`
  - obligation `lyapunov_fourth_moment_bound` `proof_debt_support`: status `open`, landing `ex_14_4_3_LyapunovVerification`, landing problem `non_theorem_landing`, child `obl_ex_14_4_3_lyapunov_fourth_moment_bound` `FAILED_LOCAL` output `False`
- `prob_14_1` ch14 `FAILED_LOCAL` `ToyApollo/Output/prob_14_1.lean` `obligation_resolution`: `ledger_status:FAILED_LOCAL`, `open_obligations`
  - open: `obligation_1, obligation_4`
  - obligation `obligation_1` `proof_debt_support`: status `open`, landing `prob_14_1_PolyaUrnBetaSetup.polya_white_count_mass / prob_14_1_white_count_mass`, landing problem `theorem_wrapper_over_structure_field`, child `obl_prob_14_1_obligation_1` `FAILED_LOCAL` output `False`
  - obligation `obligation_4` `proof_debt_support`: status `open`, landing `prob_14_1_PolyaUrnBetaSetup.stirling_cdf_convergence / prob_14_1_stirling_beta_cdf_convergence`, landing problem `theorem_wrapper_over_structure_field`, child `obl_prob_14_1_obligation_4` `FAILED_LOCAL` output `False`
- `prob_14_10` ch14 `FAILED_LOCAL` `ToyApollo/Output/prob_14_10.lean` `obligation_resolution`: `ledger_status:FAILED_LOCAL`, `open_obligations`
  - open: `obligation_4`
  - obligation `obligation_4` `proof_debt_support`: status `open`, landing `prob_14_10_BoundedMomentSetup.moments_to_mgf_setup`, landing problem `structure_field_landing`, child `obl_prob_14_10_obligation_4` `FAILED_LOCAL` output `False`
- `prob_14_11` ch14 `FAILED_LOCAL` `ToyApollo/Output/prob_14_11.lean` `obligation_resolution`: `ledger_status:FAILED_LOCAL`, `open_obligations`
  - open: `obligation_2, obligation_3, obligation_4`
  - obligation `obligation_2` `proof_debt_support`: status `open`, landing `prob_14_11_CouponRatioTriangularArraySetup.theoremSetup / source_rows_are_independent / source_coupon_collection_law_is_stage_sum`, landing problem `structure_field_landing`, child `obl_prob_14_11_obligation_2` `FAILED_LOCAL` output `False`
  - obligation `obligation_3` `proof_debt_support`: status `open`, landing `prob_14_11_asymptoticMeanScale / prob_14_11_asymptoticVarianceScale / mean_asymptotic / variance_asymptotic`, landing problem `missing_theorem_or_lemma_landing`, child `obl_prob_14_11_obligation_3` `FAILED_LOCAL` output `False`
  - obligation `obligation_4` `proof_debt_support`: status `open`, landing `prob_14_11_CouponRatioTriangularArraySetup.generalized_lyapunov_condition`, landing problem `structure_field_landing`, child `obl_prob_14_11_obligation_4` `FAILED_LOCAL` output `False`
- `prob_14_8` ch14 `FAILED_LOCAL` `ToyApollo/Output/prob_14_8.lean` `obligation_resolution`: `ledger_status:FAILED_LOCAL`, `open_obligations`
  - open: `obligation_4`
  - obligation `obligation_4` `proof_debt_support`: status `open`, landing `prob_14_8_MgfConvergenceSetup.mgf_to_characteristic_convergence / prob_14_8_characteristic_convergence`, landing problem `theorem_wrapper_over_structure_field`, child `obl_prob_14_8_obligation_4` `FAILED_LOCAL` output `False`
- `thm_14_7` ch14 `FAILED_LOCAL` `ToyApollo/Output/thm_14_7.lean` `obligation_resolution`: `ledger_status:FAILED_LOCAL`, `open_obligations`
  - open: `center_and_standardize, quadratic_characteristic_expansion, independent_sum_characteristic`
  - obligation `center_and_standardize` `proof_debt_support`: status `open`, landing `thm_14_7_LindebergLevySetup.mean, thm_14_7_LindebergLevySetup.sigma, thm_14_7_LindebergLevySetup.standardizedLaws`, landing problem `structure_field_landing`, child `obl_thm_14_7_center_and_standardize` `FAILED_LOCAL` output `False`
  - obligation `quadratic_characteristic_expansion` `proof_debt_support`: status `open`, landing `thm_14_7_quadraticCharacteristicExpansion, thm_14_7_LindebergLevySetup.quadratic_expansion`, landing problem `structure_field_landing`, child `obl_thm_14_7_quadratic_characteristic_expansion` `FAILED_LOCAL` output `False`
  - obligation `independent_sum_characteristic` `proof_debt_support`: status `open`, landing `thm_14_7_LindebergLevySetup.c, thm_14_7_LindebergLevySetup.c_definition`, landing problem `structure_field_landing`, child `obl_thm_14_7_independent_sum_characteristic` `FAILED_LOCAL` output `False`
- `thm_14_8` ch14 `COMPLETED_WITH_PROOF_DEBT` `ToyApollo/Output/thm_14_8.lean` `allowed_beyond_book_hygiene`: `ledger_status:COMPLETED_WITH_PROOF_DEBT`, `completed_with_proof_debt`

## Orphan Output Files

- `thm_9_5_dirichlet` ch9 `ToyApollo/Output/thm_9_5_dirichlet.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_9_5_kernel`
- `thm_9_5_fubini` ch9 `ToyApollo/Output/thm_9_5_fubini.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_9_5_kernel`
- `thm_9_5_kernel` ch9 `ToyApollo/Output/thm_9_5_kernel.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_9_5`
- `prob_10_10_distribution_bridge` ch10 `ToyApollo/Output/prob_10_10_distribution_bridge.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `(none)`
- `thm_10_8_inverse_comparison` ch10 `ToyApollo/Output/thm_10_8_inverse_comparison.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_10_8_quantile_convergence`
- `thm_10_8_quantile_convergence` ch10 `ToyApollo/Output/thm_10_8_quantile_convergence.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_10_8`
- `thm_10_8_quantile_defs` ch10 `ToyApollo/Output/thm_10_8_quantile_defs.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_10_8, thm_10_8_inverse_comparison, thm_10_8_quantile_law`
- `thm_10_8_quantile_law` ch10 `ToyApollo/Output/thm_10_8_quantile_law.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_10_8`
- `thm_10_8_quantile_space` ch10 `ToyApollo/Output/thm_10_8_quantile_space.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_10_8_quantile_defs`
- `thm_14_4_dominating_measure` ch14 `ToyApollo/Output/thm_14_4_dominating_measure.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_14_4`
