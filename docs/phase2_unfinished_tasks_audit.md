# Phase2 Unfinished Task Audit

- Generated at: `2026-06-22T06:34:26.154369Z`
- Scope: chapters `9`-`14`
- Extra included tasks: `thm_6_7__lemma_1`
- Task filter: `(none)`
- Bucket filter: `(none)`
- Build checked: `True`
- Build timeout seconds: `360`
- Unfinished or verify count: `3`
- Blocking unfinished count: `0`
- Verification-only count: `1`
- Allowed-exception boundary count: `2`
- Orphan output count: `59`

## Reason Counts

- `allowed_exception_boundary`: 2
- `critical_ch6_bridge_verify`: 1

## Interpretation Notes

- blocking_unfinished_count excludes verification-only items and explicit allowed-exception boundaries.
- allowed_exception_boundary items remain visible and are not ordinary clean proof completion.
- A zero blocking_unfinished_count does not claim external or beyond-book mathematics has been locally proved.

## Build Status Counts

- `ok`: 3

## Repair Batches

- `critical_bridge_verification` (1): `thm_6_7__lemma_1`
  - action: Build-check the Chapter 6 bridge and keep it in the report as a critical dependency, even though it is already completed.
- `allowed_exception_boundary` (2): `thm_11_8, thm_14_8`
  - action: Keep the explicit allowed exception visible, but do not count it as unfinished proof debt.

## Tasks

- `thm_6_7__lemma_1` ch6 `COMPLETED` `ToyApollo/Output/thm_6_7__lemma_1.lean` `critical_bridge_verification`: `critical_ch6_bridge_verify`
  - build: `ok`
- `thm_11_8` ch11 `COMPLETED` `ToyApollo/Output/thm_11_8.lean` `allowed_exception_boundary`: `allowed_exception_boundary`
  - build: `ok`
- `thm_14_8` ch14 `COMPLETED_WITH_PROOF_DEBT` `ToyApollo/Output/thm_14_8.lean` `allowed_exception_boundary`: `allowed_exception_boundary`
  - build: `ok`

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
- `thm_11_7_support` ch11 `ToyApollo/Output/thm_11_7_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_11_7`
- `ex_13_6_5_aabb_support` ch13 `ToyApollo/Output/ex_13_6_5_aabb_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_optional_stopping_support`
- `ex_13_6_5_abab_support` ch13 `ToyApollo/Output/ex_13_6_5_abab_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_optional_stopping_support`
- `ex_13_6_5_base_support` ch13 `ToyApollo/Output/ex_13_6_5_base_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_waiting_time_support`
- `ex_13_6_5_optional_stopping_support` ch13 `ToyApollo/Output/ex_13_6_5_optional_stopping_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5`
- `ex_13_6_5_process_common_support` ch13 `ToyApollo/Output/ex_13_6_5_process_common_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_word_pattern_support`
- `ex_13_6_5_waiting_time_support` ch13 `ToyApollo/Output/ex_13_6_5_waiting_time_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_process_common_support`
- `ex_13_6_5_word_pattern_support` ch13 `ToyApollo/Output/ex_13_6_5_word_pattern_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_13_6_5_aabb_support, ex_13_6_5_abab_support`
- `prob_13_10_centered_wald_support` ch13 `ToyApollo/Output/prob_13_10_centered_wald_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_13_10`
- `prob_13_10_independent_count_support` ch13 `ToyApollo/Output/prob_13_10_independent_count_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_13_10_centered_wald_support, prob_13_10_relaxed_optional_stopping_support`
- `prob_13_10_relaxed_optional_stopping_support` ch13 `ToyApollo/Output/prob_13_10_relaxed_optional_stopping_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_13_10_centered_wald_support`
- `prob_13_10_stopped_sum_support` ch13 `ToyApollo/Output/prob_13_10_stopped_sum_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_13_10_independent_count_support`
- `thm_13_12_support` ch13 `ToyApollo/Output/thm_13_12_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_13_12`
- `thm_13_14_support` ch13 `ToyApollo/Output/thm_13_14_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_13_14`
- `thm_13_18_support` ch13 `ToyApollo/Output/thm_13_18_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_13_18`
- `thm_13_3_l2_support` ch13 `ToyApollo/Output/thm_13_3_l2_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_13_3`
- `ex_14_4_1_binomial_support` ch14 `ToyApollo/Output/ex_14_4_1_binomial_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_14_4_1_proof_support`
- `ex_14_4_1_proof_support` ch14 `ToyApollo/Output/ex_14_4_1_proof_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_14_4_1`
- `ex_14_4_1_source_support` ch14 `ToyApollo/Output/ex_14_4_1_source_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_14_4_1_binomial_support`
- `ex_14_4_3_coupon_stage_support` ch14 `ToyApollo/Output/ex_14_4_3_coupon_stage_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `ex_14_4_3`
- `prob_14_11_support` ch14 `ToyApollo/Output/prob_14_11_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_11`
- `prob_14_12_limit_truncation_tail_support` ch14 `ToyApollo/Output/prob_14_12_limit_truncation_tail_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_12_mean_convergence_support`
- `prob_14_12_mean_convergence_support` ch14 `ToyApollo/Output/prob_14_12_mean_convergence_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_12`
- `prob_14_1_asymptotic_support` ch14 `ToyApollo/Output/prob_14_1_asymptotic_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1_finite_law_support`
- `prob_14_1_finite_law_support` ch14 `ToyApollo/Output/prob_14_1_finite_law_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1_grid_cdf_support`
- `prob_14_1_grid_cdf_support` ch14 `ToyApollo/Output/prob_14_1_grid_cdf_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1_tail_riemann_support`
- `prob_14_1_proof_support` ch14 `ToyApollo/Output/prob_14_1_proof_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1`
- `prob_14_1_tail_endpoint_support` ch14 `ToyApollo/Output/prob_14_1_tail_endpoint_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1_tail_support`
- `prob_14_1_tail_riemann_support` ch14 `ToyApollo/Output/prob_14_1_tail_riemann_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1_tail_endpoint_support`
- `prob_14_1_tail_support` ch14 `ToyApollo/Output/prob_14_1_tail_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_1_proof_support`
- `prob_14_8_mgf_support` ch14 `ToyApollo/Output/prob_14_8_mgf_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_8_proof_support`
- `prob_14_8_montel_support` ch14 `ToyApollo/Output/prob_14_8_montel_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_8_mgf_support`
- `prob_14_8_proof_support` ch14 `ToyApollo/Output/prob_14_8_proof_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_8`
- `prob_14_8_subseq_support` ch14 `ToyApollo/Output/prob_14_8_subseq_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `prob_14_8_montel_support`
- `thm_14_4_density_support` ch14 `ToyApollo/Output/thm_14_4_density_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_14_4`
- `thm_14_4_dominating_measure` ch14 `ToyApollo/Output/thm_14_4_dominating_measure.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_14_4_density_support`
- `thm_14_5_support` ch14 `ToyApollo/Output/thm_14_5_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_14_5`
- `thm_14_7_support` ch14 `ToyApollo/Output/thm_14_7_support.lean`: `missing_ledger_entry`; `prompt_pack=no`; imported by `thm_14_7`
