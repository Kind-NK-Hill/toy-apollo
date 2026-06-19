# Phase2 Unfinished Task Audit

- Generated at: `2026-06-19T02:58:15.803214Z`
- Scope: chapters `9`-`14`
- Extra included tasks: `thm_6_7__lemma_1`
- Task filter: `(none)`
- Bucket filter: `(none)`
- Build checked: `False`
- Build timeout seconds: `120`
- Unfinished or verify count: `9`
- Blocking unfinished count: `8`
- Verification-only count: `1`
- Orphan output count: `49`

## Reason Counts

- `completed_with_proof_debt`: 1
- `critical_ch6_bridge_verify`: 1
- `ledger_status:COMPLETED_WITH_PROOF_DEBT`: 1
- `open_obligations`: 7
- `public_surface_error`: 3

## Open Obligation Kinds

- `proof_debt_support`: 14
- `source_step`: 6
- `interface-name matches`: 0
- `structure-field landings`: 10
- `theorem wrappers over structure fields`: 0
- `empty landings`: 0
- `ledger-only child obligations`: 0

## Repair Batches

- `critical_bridge_verification` (1): `thm_6_7__lemma_1`
  - action: Build-check the Chapter 6 bridge and keep it in the report as a critical dependency, even though it is already completed.
- `public_surface_and_obligations` (2): `thm_14_5, thm_14_7`
  - action: First remove public Support/Spine parameters, then close the named proof obligations with theorem-level landings.
- `public_surface_cleanup` (1): `prob_14_1`
  - action: Remove public Support/Spine parameters or make support-consuming helpers private; no open obligation is recorded.
- `obligation_resolution` (5): `prob_10_10, prob_11_9, thm_11_8, thm_13_12, thm_14_8`
  - action: Resolve the open proof obligations and land them on theorem/lemma declarations rather than structure fields.

## Tasks

- `thm_6_7__lemma_1` ch6 `COMPLETED` `ToyApollo/Output/thm_6_7__lemma_1.lean` `critical_bridge_verification`: `critical_ch6_bridge_verify`
- `prob_10_10` ch10 `COMPLETED` `ToyApollo/Output/prob_10_10.lean` `obligation_resolution`: `open_obligations`
  - open: `distribution_stability_under_probability_perturbation`
  - obligation `distribution_stability_under_probability_perturbation` `proof_debt_support`: status `proved`, landing `h_add_perturbation_support, h_mul_perturbation_support`, landing problem `missing_theorem_or_lemma_landing`
- `prob_11_9` ch11 `COMPLETED` `ToyApollo/Output/prob_11_9.lean` `obligation_resolution`: `open_obligations`
  - open: `asymptotic_regime`
  - obligation `asymptotic_regime` `source_step`: status `partial`, landing `prob_11_9_asymptoticRegime`, landing problem `non_theorem_landing`
- `thm_11_8` ch11 `COMPLETED` `ToyApollo/Output/thm_11_8.lean` `obligation_resolution`: `open_obligations`
  - open: `etemadi_external_proof_bridge`
  - obligation `etemadi_external_proof_bridge` `source_step`: status `accepted_as_proof_debt`, landing `ProbabilityTheory.strong_law_ae`, landing problem `missing_theorem_or_lemma_landing`
- `thm_13_12` ch13 `COMPLETED` `ToyApollo/Output/thm_13_12.lean` `obligation_resolution`: `open_obligations`
  - open: `countable_partition_and_generated_sigma`
  - obligation `countable_partition_and_generated_sigma` `source_step`: status `partial`, landing `thm_13_12_countablePartition, thm_13_12_generatedByPartition`, landing problem `non_theorem_landing`
- `prob_14_1` ch14 `COMPLETED` `ToyApollo/Output/prob_14_1.lean` `public_surface_cleanup`: `public_surface_error`
- `thm_14_5` ch14 `COMPLETED` `ToyApollo/Output/thm_14_5.lean` `public_surface_and_obligations`: `open_obligations`, `public_surface_error`
  - open: `characteristic_at_zero, fubini_identity, inner_integral_identity, averaged_kernel_identity, kernel_tail_lower_bound, tail_bound_by_averaged_characteristic, continuity_small_u_bound, dominated_convergence_bound, finite_prefix_tail_bound, uniform_tail_bound`
  - obligation `characteristic_at_zero` `proof_debt_support`: status `proved`, landing `thm_14_5_SourceProofSpine.characteristic_at_zero (structure field only; theorem-level source proof still missing)`, landing problem `structure_field_landing`
  - obligation `fubini_identity` `proof_debt_support`: status `proved`, landing `thm_14_5_SourceProofSpine.fubini_identity (structure field only; theorem-level source proof still missing)`, landing problem `structure_field_landing`
  - obligation `inner_integral_identity` `proof_debt_support`: status `proved`, landing `thm_14_5_SourceProofSpine.inner_integral_identity (structure field only; theorem-level source proof still missing)`, landing problem `structure_field_landing`
  - obligation `averaged_kernel_identity` `proof_debt_support`: status `proved`, landing `thm_14_5_SourceProofSpine.averaged_kernel_identity (structure field only; theorem-level source proof still missing)`, landing problem `structure_field_landing`
  - obligation `kernel_tail_lower_bound` `proof_debt_support`: status `proved`, landing `thm_14_5_SourceProofSpine.kernel_tail_lower_bound (structure field only; theorem-level source proof still missing)`, landing problem `structure_field_landing`
  - obligation `tail_bound_by_averaged_characteristic` `proof_debt_support`: status `proved`, landing `thm_14_5_SourceProofSpine.tail_bound_by_averaged_characteristic (structure field only; theorem-level source proof still missing)`, landing problem `structure_field_landing`
  - obligation `continuity_small_u_bound` `proof_debt_support`: status `proved`, landing `thm_14_5_SourceProofSpine.continuity_small_u_bound (structure field only; theorem-level source proof still missing)`, landing problem `structure_field_landing`
  - obligation `dominated_convergence_bound` `proof_debt_support`: status `proved`, landing `thm_14_5_SourceProofSpine.dominated_convergence_bound (structure field only; theorem-level source proof still missing)`, landing problem `structure_field_landing`
  - obligation `finite_prefix_tail_bound` `proof_debt_support`: status `proved`, landing `thm_14_5_SourceProofSpine.finite_prefix_tail_bound (structure field only; theorem-level source proof still missing)`, landing problem `structure_field_landing`
  - obligation `uniform_tail_bound` `proof_debt_support`: status `proved`, landing `thm_14_5_SourceProofSpine.uniform_tail_bound (structure field only; theorem-level source proof still missing)`, landing problem `structure_field_landing`
- `thm_14_7` ch14 `COMPLETED` `ToyApollo/Output/thm_14_7.lean` `public_surface_and_obligations`: `open_obligations`, `public_surface_error`
  - open: `center_and_standardize, quadratic_characteristic_expansion, independent_sum_characteristic`
  - obligation `center_and_standardize` `proof_debt_support`: status `proved`, landing `thm_14_7_LindebergLevySetup.mean, thm_14_7_LindebergLevySetup.sigma, thm_14_7_LindebergLevySetup.standardizedLaws`, landing problem `missing_theorem_or_lemma_landing`
  - obligation `quadratic_characteristic_expansion` `proof_debt_support`: status `proved`, landing `thm_14_7_quadraticCharacteristicExpansion; thm_14_7_quadratic_characteristic_expansion_internal`, landing problem `missing_theorem_or_lemma_landing`
  - obligation `independent_sum_characteristic` `proof_debt_support`: status `proved`, landing `thm_14_7_LindebergLevySetup.c, thm_14_7_LindebergLevySetup.c_definition`, landing problem `missing_theorem_or_lemma_landing`
- `thm_14_8` ch14 `COMPLETED_WITH_PROOF_DEBT` `ToyApollo/Output/thm_14_8.lean` `obligation_resolution`: `ledger_status:COMPLETED_WITH_PROOF_DEBT`, `completed_with_proof_debt`, `open_obligations`
  - open: `triangular_array_setup, lindeberg_condition, lyapunov_condition`
  - obligation `triangular_array_setup` `source_step`: status `partial`, landing `thm_14_8_TriangularArraySetup`, landing problem `non_theorem_landing`
  - obligation `lindeberg_condition` `source_step`: status `partial`, landing `thm_14_8_lindebergTailIntegral; thm_14_8_LindebergCondition`, landing problem `non_theorem_landing`
  - obligation `lyapunov_condition` `source_step`: status `partial`, landing `thm_14_8_lyapunovMoment; thm_14_8_LyapunovCondition`, landing problem `non_theorem_landing`

## Orphan Output Files

- `prob_9_3_basic_support` ch9 `ToyApollo/Output/prob_9_3_basic_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_9_3_kernel_support`
- `prob_9_3_final_support` ch9 `ToyApollo/Output/prob_9_3_final_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_9_3_proof_support`
- `prob_9_3_fourier_support` ch9 `ToyApollo/Output/prob_9_3_fourier_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_9_3_law_support`
- `prob_9_3_kernel_support` ch9 `ToyApollo/Output/prob_9_3_kernel_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_9_3_fourier_support`
- `prob_9_3_law_support` ch9 `ToyApollo/Output/prob_9_3_law_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_9_3_final_support`
- `prob_9_3_proof_support` ch9 `ToyApollo/Output/prob_9_3_proof_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_9_3`
- `thm_9_5_dirichlet` ch9 `ToyApollo/Output/thm_9_5_dirichlet.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_9_5_kernel`
- `thm_9_5_fubini` ch9 `ToyApollo/Output/thm_9_5_fubini.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_9_5_kernel`
- `thm_9_5_kernel` ch9 `ToyApollo/Output/thm_9_5_kernel.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_9_5`
- `prob_10_10_distribution_bridge` ch10 `ToyApollo/Output/prob_10_10_distribution_bridge.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `(none)`
- `thm_10_8_inverse_comparison` ch10 `ToyApollo/Output/thm_10_8_inverse_comparison.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_10_8_quantile_convergence`
- `thm_10_8_quantile_convergence` ch10 `ToyApollo/Output/thm_10_8_quantile_convergence.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_10_8`
- `thm_10_8_quantile_defs` ch10 `ToyApollo/Output/thm_10_8_quantile_defs.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_10_8, thm_10_8_inverse_comparison, thm_10_8_quantile_law`
- `thm_10_8_quantile_law` ch10 `ToyApollo/Output/thm_10_8_quantile_law.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_10_8`
- `thm_10_8_quantile_space` ch10 `ToyApollo/Output/thm_10_8_quantile_space.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_10_8_quantile_defs`
- `prob_11_9_final_support` ch11 `ToyApollo/Output/prob_11_9_final_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_11_9_proof_support`
- `prob_11_9_limit_support` ch11 `ToyApollo/Output/prob_11_9_limit_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_11_9_probability_support`
- `prob_11_9_model_support` ch11 `ToyApollo/Output/prob_11_9_model_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_11_9_moment_support`
- `prob_11_9_moment_support` ch11 `ToyApollo/Output/prob_11_9_moment_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_11_9_limit_support`
- `prob_11_9_probability_support` ch11 `ToyApollo/Output/prob_11_9_probability_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_11_9_final_support`
- `prob_11_9_proof_support` ch11 `ToyApollo/Output/prob_11_9_proof_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_11_9`
- `ex_13_6_5_aabb_support` ch13 `ToyApollo/Output/ex_13_6_5_aabb_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_optional_stopping_support`
- `ex_13_6_5_abab_support` ch13 `ToyApollo/Output/ex_13_6_5_abab_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_optional_stopping_support`
- `ex_13_6_5_base_support` ch13 `ToyApollo/Output/ex_13_6_5_base_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_waiting_time_support`
- `ex_13_6_5_optional_stopping_support` ch13 `ToyApollo/Output/ex_13_6_5_optional_stopping_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5`
- `ex_13_6_5_process_common_support` ch13 `ToyApollo/Output/ex_13_6_5_process_common_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_aabb_support, ex_13_6_5_abab_support`
- `ex_13_6_5_waiting_time_support` ch13 `ToyApollo/Output/ex_13_6_5_waiting_time_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_process_common_support`
- `prob_13_10_centered_wald_support` ch13 `ToyApollo/Output/prob_13_10_centered_wald_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_13_10`
- `prob_13_10_independent_count_support` ch13 `ToyApollo/Output/prob_13_10_independent_count_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_13_10_centered_wald_support, prob_13_10_relaxed_optional_stopping_support`
- `prob_13_10_relaxed_optional_stopping_support` ch13 `ToyApollo/Output/prob_13_10_relaxed_optional_stopping_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_13_10_centered_wald_support`
- `prob_13_10_stopped_sum_support` ch13 `ToyApollo/Output/prob_13_10_stopped_sum_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_13_10_independent_count_support`
- `thm_13_3_l2_support` ch13 `ToyApollo/Output/thm_13_3_l2_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_13_3`
- `ex_14_4_1_binomial_support` ch14 `ToyApollo/Output/ex_14_4_1_binomial_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_14_4_1_proof_support`
- `ex_14_4_1_proof_support` ch14 `ToyApollo/Output/ex_14_4_1_proof_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_14_4_1`
- `ex_14_4_1_source_support` ch14 `ToyApollo/Output/ex_14_4_1_source_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_14_4_1_binomial_support`
- `ex_14_4_3_coupon_stage_support` ch14 `ToyApollo/Output/ex_14_4_3_coupon_stage_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_14_4_3`
- `prob_14_12_limit_truncation_tail_support` ch14 `ToyApollo/Output/prob_14_12_limit_truncation_tail_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_12_mean_convergence_support`
- `prob_14_12_mean_convergence_support` ch14 `ToyApollo/Output/prob_14_12_mean_convergence_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_12`
- `prob_14_1_asymptotic_support` ch14 `ToyApollo/Output/prob_14_1_asymptotic_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1_finite_law_support`
- `prob_14_1_finite_law_support` ch14 `ToyApollo/Output/prob_14_1_finite_law_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1_grid_cdf_support`
- `prob_14_1_grid_cdf_support` ch14 `ToyApollo/Output/prob_14_1_grid_cdf_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1_tail_support`
- `prob_14_1_proof_support` ch14 `ToyApollo/Output/prob_14_1_proof_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1`
- `prob_14_1_tail_support` ch14 `ToyApollo/Output/prob_14_1_tail_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1_proof_support`
- `prob_14_8_mgf_support` ch14 `ToyApollo/Output/prob_14_8_mgf_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_8_proof_support`
- `prob_14_8_montel_support` ch14 `ToyApollo/Output/prob_14_8_montel_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_8_mgf_support`
- `prob_14_8_proof_support` ch14 `ToyApollo/Output/prob_14_8_proof_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_8`
- `prob_14_8_subseq_support` ch14 `ToyApollo/Output/prob_14_8_subseq_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_8_montel_support`
- `thm_14_4_density_support` ch14 `ToyApollo/Output/thm_14_4_density_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_14_4`
- `thm_14_4_dominating_measure` ch14 `ToyApollo/Output/thm_14_4_dominating_measure.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_14_4_density_support`
