# Phase2 Step 5.6 Contract Reconciliation Report

Created: 2026-05-25

Scope: reconcile Step 5.5 contract metadata and classification state without Lean proof edits or manual ledger edits.

## Executive Result

- Starting Step 5.5 global contract audit error count: `2089`.
- Ending global contract audit error count: `2027`.
- Ending warning count: `50`.
- Ending error task count: `136`.
- Strict classification gate: `passes` after JSON reconciliation.
- Lean proof files edited: `no`.
- `project_ledger.json` edited: `no`.

The corpus is not globally contract-clean yet, but the Step 6 priority tasks were reconciled and the remaining queue is explicit below.

## Cleaned Priority Tasks

| task | result | note |
| --- | --- | --- |
| `prob_10_6` | task audit `0 error / 0 warning` | Two obligations now have checked `verified` proof contracts against theorem-level Lean landings. |
| `thm_11_7` | task audit `0 error / 0 warning` | Public-premise tail-summability gap is open debt; interface rows are not marked proved. |
| `thm_13_14` | task audit `0 error / 0 warning` | Interval Fubini and pi-lambda extension remain open public-premise debt; downstream assembly is not marked verified. |
| `thm_14_5` | task audit `0 error / 0 warning` | Source-route proof spine remains open; current public theorem is adapter-classified, not textbook proof completed. |
| `thm_14_8` | task audit `0 error / 0 warning` | Beyond-book root exception remains accepted debt, not ordinary proved obligation. |
| `ex_14_4_3` | task audit `0 error / 0 warning` | Inherited beyond-book use is separated from local Lyapunov private-axiom debt. |

## Classification Reconciliation

- `prob_10_6` remains `textbook_proof_completed` with proof-contract validation evidence.
- `ex_14_3_1` and `ex_14_3_2` remain `textbook_proof_completed` as Level 0 direct statement/setup rows with no task-local proof obligations in scope.
- The following earlier Good Corpus `textbook_proof_completed` rows are now `needs_decision` because they lack verified strict proof-contract evidence:

- `ex_10_3_2`
- `thm_10_8`
- `prob_11_5`
- `prob_11_7`
- `ex_13_5_1`
- `thm_13_12`
- `thm_13_13`
- `prob_14_3`
- `prob_14_4`
- `prob_14_7`
- `prob_14_9`

## Remaining Error Categories

| category | count | interpretation |
| --- | ---: | --- |
| `accepted_debt_missing_contract_note` | 1 | metadata note missing for accepted debt |
| `landing_not_found_in_output` | 37 | proved landing not found by Lean declaration scan; now an error for proved obligations |
| `non_exception_beyond_book` | 1 | beyond-book marker outside the single allowed root exception |
| `open_missing_expected_signature` | 46 | open/partial blocking obligation lacks a target signature |
| `proved_body_reassumption_not_passed` | 378 | proved obligation lacks body anti-reassumption check |
| `proved_contract_not_verified` | 378 | proved obligation lacks verified contract status |
| `proved_forbidden_landing_kind` | 102 | proved obligation lands on forbidden kind such as structure/support/private axiom/adapter |
| `proved_missing_expected_signature` | 378 | proved obligation lacks expected theorem signature |
| `proved_public_premise_not_passed` | 378 | proved obligation lacks public-premise relocation check |
| `proved_signature_not_passed` | 378 | proved obligation lacks signature-match check |

## Metadata-Reconciliation Queue

These tasks currently have only missing proof-contract metadata/check categories. They may be metadata-fixable, but only after source/Lean signature review; do not bulk-fill `verified`.

- Task count: `83`

- `ex_10_1_1`
- `ex_10_2_1`
- `ex_10_2_2`
- `ex_10_3_1`
- `ex_10_3_2`
- `ex_10_3_3`
- `ex_10_5_1`
- `ex_13_3_1`
- `obl_ex_13_5_1_pi_lambda_extension`
- `obl_ex_13_5_1_rectangle_area`
- `obl_ex_13_6_5_expected_waiting_times`
- `obl_ex_13_6_5_optional_stopping_zero_gain`
- `obl_prob_10_10_constant_distribution_to_probability`
- `obl_prob_11_4_density_mean_interface`
- `obl_prob_11_5_tail_summability_support`
- `obl_prob_11_6_tail_summability_support`
- `obl_prob_11_7_variance_decay_support`
- `obl_prob_14_10_obligation_3`
- `obl_prob_14_1_obligation_2`
- `obl_prob_14_2_gamma_sum_representation`
- `obl_prob_14_3_obligation_2`
- `obl_prob_14_3_obligation_4`
- `obl_prob_14_4_obligation_2`
- `obl_prob_14_5_obligation_3`
- `obl_prob_14_5_obligation_4`
- `obl_prob_14_5_obligation_5`
- `obl_prob_14_6_obligation_1`
- `obl_prob_14_6_obligation_2`
- `obl_prob_14_6_obligation_3`
- `obl_prob_14_7_obligation_1`
- `obl_prob_14_7_obligation_2`
- `obl_prob_14_7_obligation_3`
- `obl_prob_14_9_obligation_3`
- `obl_prob_14_9_obligation_4`
- `obl_thm_10_8_almost_sure_quantile_convergence`
- `obl_thm_10_8_quantile_event_measurability`
- `obl_thm_10_8_upper_lower_inverse_comparison`
- `obl_thm_13_12_candidate_satisfies_def_13_3`
- `obl_thm_14_2_distribution_to_weak`
- `obl_thm_14_6_inversion_formula_identification`
- `obl_thm_14_6_real_analysis_subsequence_principle`
- `obl_thm_14_6_subsequence_characteristic_limit`
- `obl_thm_14_6_subsubsequence_test_integral_limit`
- `obl_thm_14_6_theorem_14_3_characteristic_limit`
- `prob_10_10`
- `prob_11_1`
- `prob_11_2`
- `prob_11_4`
- `prob_11_5`
- `prob_11_7`
- `prob_12_2`
- `prob_13_5`
- `prob_13_7`
- `prob_14_6`
- `prob_14_7`
- `thm_10_10`
- `thm_10_11`
- `thm_10_2`
- `thm_10_4`
- `thm_10_5`
- `thm_10_6`
- `thm_10_7`
- `thm_11_1`
- `thm_11_2`
- `thm_11_3`
- `thm_11_4`
- `thm_12_2`
- `thm_12_3`
- `thm_12_4`
- `thm_12_5`
- `thm_12_6`
- `thm_13_1`
- `thm_13_10`
- `thm_13_11`
- `thm_13_13`
- `thm_13_16`
- `thm_13_17`
- `thm_13_4`
- `thm_13_6`
- `thm_13_7`
- `thm_13_8`
- `thm_13_9`
- `thm_9_6`

## Lean Proof Or Statement-Decision Queue

These tasks have forbidden landing kinds, missing Lean landings, beyond-book boundary issues, or other evidence that requires proof work, statement decision, adapter classification, or source-route redesign before clean contract closure.

- Task count: `53`

- `ex_11_5_1`
- `ex_11_5_2`
- `ex_12_2_2`
- `ex_12_2_3`
- `ex_12_4_1`
- `ex_12_4_2`
- `ex_12_4_3`
- `ex_13_5_1`
- `ex_13_6_3`
- `ex_13_6_5`
- `ex_14_4_2`
- `obl_ex_10_3_2_gaussian_density_special_case`
- `obl_prob_10_10_distribution_stability_under_probability_perturbation`
- `obl_prob_14_12_obligation_2`
- `obl_prob_14_12_obligation_3`
- `obl_prob_14_12_obligation_5`
- `obl_prob_14_1_obligation_3`
- `obl_thm_13_18_bounded_increment_case`
- `obl_thm_13_18_uniform_bound_case`
- `obl_thm_14_8_beyond_book_proof_obligations`
- `prob_10_2`
- `prob_10_7`
- `prob_11_10`
- `prob_11_3`
- `prob_11_6`
- `prob_11_8`
- `prob_11_9`
- `prob_14_1`
- `prob_14_10`
- `prob_14_11`
- `prob_14_12`
- `prob_14_2`
- `prob_14_3`
- `prob_14_4`
- `prob_14_5`
- `prob_14_8`
- `prob_14_9`
- `thm_10_1`
- `thm_10_8`
- `thm_10_9`
- `thm_11_5`
- `thm_11_6`
- `thm_11_8`
- `thm_13_12`
- `thm_13_15`
- `thm_13_18`
- `thm_13_2`
- `thm_14_1`
- `thm_14_2`
- `thm_14_4`
- `thm_14_6`
- `thm_14_7`
- `thm_9_5`

## Warning-Only Queue

These tasks do not currently have contract errors but still have warnings such as open expected-signature gaps or accepted-debt notes.

- Task count: `31`

- `ex_14_4_1`
- `obl_ex_14_4_3_lyapunov_fourth_moment_bound`
- `obl_prob_11_10_continuous_grid_uniformization`
- `obl_prob_11_6_sixth_moment_support`
- `obl_prob_11_8_covariance_decay_support`
- `obl_prob_11_9_occupancy_moment_calculation`
- `obl_prob_14_10_obligation_4`
- `obl_prob_14_11_obligation_2`
- `obl_prob_14_11_obligation_3`
- `obl_prob_14_11_obligation_4`
- `obl_prob_14_1_obligation_1`
- `obl_prob_14_1_obligation_4`
- `obl_prob_14_8_obligation_4`
- `obl_thm_11_7_fourth_moment_expansion_tail_bound`
- `obl_thm_13_14_interval_fubini_calculation`
- `obl_thm_13_14_pi_lambda_extension`
- `obl_thm_14_5_averaged_kernel_identity`
- `obl_thm_14_5_characteristic_at_zero`
- `obl_thm_14_5_continuity_small_u_bound`
- `obl_thm_14_5_dominated_convergence_bound`
- `obl_thm_14_5_finite_prefix_tail_bound`
- `obl_thm_14_5_fubini_identity`
- `obl_thm_14_5_inner_integral_identity`
- `obl_thm_14_5_kernel_tail_lower_bound`
- `obl_thm_14_5_tail_bound_by_averaged_characteristic`
- `obl_thm_14_5_uniform_tail_bound`
- `obl_thm_14_7_center_and_standardize`
- `obl_thm_14_7_independent_sum_characteristic`
- `obl_thm_14_7_quadratic_characteristic_expansion`
- `prob_10_5`
- `thm_10_12`

## Remaining Error Task Detail

| task | categories | next queue |
| --- | --- | --- |
| `ex_10_1_1` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `ex_10_2_1` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `ex_10_2_2` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `ex_10_3_1` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `ex_10_3_2` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |
| `ex_10_3_3` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `ex_10_5_1` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `ex_11_5_1` | `landing_not_found_in_output`:4, `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_forbidden_landing_kind`:4, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | proof/statement decision |
| `ex_11_5_2` | `landing_not_found_in_output`:3, `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_forbidden_landing_kind`:5, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | proof/statement decision |
| `ex_12_2_2` | `proved_body_reassumption_not_passed`:6, `proved_contract_not_verified`:6, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:6, `proved_public_premise_not_passed`:6, `proved_signature_not_passed`:6 | proof/statement decision |
| `ex_12_2_3` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_forbidden_landing_kind`:3, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | proof/statement decision |
| `ex_12_4_1` | `proved_body_reassumption_not_passed`:6, `proved_contract_not_verified`:6, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:6, `proved_public_premise_not_passed`:6, `proved_signature_not_passed`:6 | proof/statement decision |
| `ex_12_4_2` | `proved_body_reassumption_not_passed`:7, `proved_contract_not_verified`:7, `proved_forbidden_landing_kind`:4, `proved_missing_expected_signature`:7, `proved_public_premise_not_passed`:7, `proved_signature_not_passed`:7 | proof/statement decision |
| `ex_12_4_3` | `proved_body_reassumption_not_passed`:7, `proved_contract_not_verified`:7, `proved_forbidden_landing_kind`:4, `proved_missing_expected_signature`:7, `proved_public_premise_not_passed`:7, `proved_signature_not_passed`:7 | proof/statement decision |
| `ex_13_3_1` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |
| `ex_13_5_1` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_forbidden_landing_kind`:3, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | proof/statement decision |
| `ex_13_6_3` | `landing_not_found_in_output`:1, `proved_body_reassumption_not_passed`:6, `proved_contract_not_verified`:6, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:6, `proved_public_premise_not_passed`:6, `proved_signature_not_passed`:6 | proof/statement decision |
| `ex_13_6_5` | `proved_body_reassumption_not_passed`:6, `proved_contract_not_verified`:6, `proved_forbidden_landing_kind`:4, `proved_missing_expected_signature`:6, `proved_public_premise_not_passed`:6, `proved_signature_not_passed`:6 | proof/statement decision |
| `ex_14_4_2` | `open_missing_expected_signature`:1, `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | proof/statement decision |
| `obl_ex_10_3_2_gaussian_density_special_case` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | proof/statement decision |
| `obl_ex_13_5_1_pi_lambda_extension` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_ex_13_5_1_rectangle_area` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_ex_13_6_5_expected_waiting_times` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_ex_13_6_5_optional_stopping_zero_gain` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_10_10_constant_distribution_to_probability` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_10_10_distribution_stability_under_probability_perturbation` | `landing_not_found_in_output`:1, `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | proof/statement decision |
| `obl_prob_11_4_density_mean_interface` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_11_5_tail_summability_support` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_11_6_tail_summability_support` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_11_7_variance_decay_support` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_10_obligation_3` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_12_obligation_2` | `landing_not_found_in_output`:1, `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | proof/statement decision |
| `obl_prob_14_12_obligation_3` | `landing_not_found_in_output`:1, `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | proof/statement decision |
| `obl_prob_14_12_obligation_5` | `landing_not_found_in_output`:1, `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | proof/statement decision |
| `obl_prob_14_1_obligation_2` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_1_obligation_3` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | proof/statement decision |
| `obl_prob_14_2_gamma_sum_representation` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_3_obligation_2` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_3_obligation_4` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_4_obligation_2` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_5_obligation_3` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_5_obligation_4` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_5_obligation_5` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_6_obligation_1` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_6_obligation_2` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_6_obligation_3` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_7_obligation_1` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_7_obligation_2` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_7_obligation_3` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_9_obligation_3` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_prob_14_9_obligation_4` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_10_8_almost_sure_quantile_convergence` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_10_8_quantile_event_measurability` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_10_8_upper_lower_inverse_comparison` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_13_12_candidate_satisfies_def_13_3` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_13_18_bounded_increment_case` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | proof/statement decision |
| `obl_thm_13_18_uniform_bound_case` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | proof/statement decision |
| `obl_thm_14_2_distribution_to_weak` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_14_6_inversion_formula_identification` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_14_6_real_analysis_subsequence_principle` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_14_6_subsequence_characteristic_limit` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_14_6_subsubsequence_test_integral_limit` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_14_6_theorem_14_3_characteristic_limit` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `obl_thm_14_8_beyond_book_proof_obligations` | `accepted_debt_missing_contract_note`:1, `non_exception_beyond_book`:1 | proof/statement decision |
| `prob_10_10` | `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | metadata review |
| `prob_10_2` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | proof/statement decision |
| `prob_10_7` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | proof/statement decision |
| `prob_11_1` | `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | metadata review |
| `prob_11_10` | `landing_not_found_in_output`:1, `open_missing_expected_signature`:1, `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_forbidden_landing_kind`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | proof/statement decision |
| `prob_11_2` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |
| `prob_11_3` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | proof/statement decision |
| `prob_11_4` | `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | metadata review |
| `prob_11_5` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `prob_11_6` | `landing_not_found_in_output`:1, `open_missing_expected_signature`:1, `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | proof/statement decision |
| `prob_11_7` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `prob_11_8` | `open_missing_expected_signature`:1, `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | proof/statement decision |
| `prob_11_9` | `landing_not_found_in_output`:1, `open_missing_expected_signature`:1, `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | proof/statement decision |
| `prob_12_2` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |
| `prob_13_5` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `prob_13_7` | `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | metadata review |
| `prob_14_1` | `open_missing_expected_signature`:2, `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | proof/statement decision |
| `prob_14_10` | `open_missing_expected_signature`:1, `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | proof/statement decision |
| `prob_14_11` | `open_missing_expected_signature`:3, `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | proof/statement decision |
| `prob_14_12` | `landing_not_found_in_output`:5, `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_forbidden_landing_kind`:5, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | proof/statement decision |
| `prob_14_2` | `open_missing_expected_signature`:1, `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | proof/statement decision |
| `prob_14_3` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | proof/statement decision |
| `prob_14_4` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | proof/statement decision |
| `prob_14_5` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | proof/statement decision |
| `prob_14_6` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |
| `prob_14_7` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | metadata review |
| `prob_14_8` | `open_missing_expected_signature`:1, `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | proof/statement decision |
| `prob_14_9` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | proof/statement decision |
| `thm_10_1` | `landing_not_found_in_output`:1, `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | proof/statement decision |
| `thm_10_10` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | metadata review |
| `thm_10_11` | `proved_body_reassumption_not_passed`:6, `proved_contract_not_verified`:6, `proved_missing_expected_signature`:6, `proved_public_premise_not_passed`:6, `proved_signature_not_passed`:6 | metadata review |
| `thm_10_2` | `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | metadata review |
| `thm_10_4` | `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | metadata review |
| `thm_10_5` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `thm_10_6` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `thm_10_7` | `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | metadata review |
| `thm_10_8` | `proved_body_reassumption_not_passed`:6, `proved_contract_not_verified`:6, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:6, `proved_public_premise_not_passed`:6, `proved_signature_not_passed`:6 | proof/statement decision |
| `thm_10_9` | `landing_not_found_in_output`:1, `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | proof/statement decision |
| `thm_11_1` | `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | metadata review |
| `thm_11_2` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | metadata review |
| `thm_11_3` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | metadata review |
| `thm_11_4` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | metadata review |
| `thm_11_5` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | proof/statement decision |
| `thm_11_6` | `landing_not_found_in_output`:2, `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_forbidden_landing_kind`:4, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | proof/statement decision |
| `thm_11_8` | `landing_not_found_in_output`:5, `proved_body_reassumption_not_passed`:6, `proved_contract_not_verified`:6, `proved_forbidden_landing_kind`:6, `proved_missing_expected_signature`:6, `proved_public_premise_not_passed`:6, `proved_signature_not_passed`:6 | proof/statement decision |
| `thm_12_2` | `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | metadata review |
| `thm_12_3` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |
| `thm_12_4` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |
| `thm_12_5` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `thm_12_6` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |
| `thm_13_1` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `thm_13_10` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `thm_13_11` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `thm_13_12` | `landing_not_found_in_output`:1, `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | proof/statement decision |
| `thm_13_13` | `proved_body_reassumption_not_passed`:1, `proved_contract_not_verified`:1, `proved_missing_expected_signature`:1, `proved_public_premise_not_passed`:1, `proved_signature_not_passed`:1 | metadata review |
| `thm_13_15` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | proof/statement decision |
| `thm_13_16` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `thm_13_17` | `proved_body_reassumption_not_passed`:6, `proved_contract_not_verified`:6, `proved_missing_expected_signature`:6, `proved_public_premise_not_passed`:6, `proved_signature_not_passed`:6 | metadata review |
| `thm_13_18` | `proved_body_reassumption_not_passed`:6, `proved_contract_not_verified`:6, `proved_forbidden_landing_kind`:3, `proved_missing_expected_signature`:6, `proved_public_premise_not_passed`:6, `proved_signature_not_passed`:6 | proof/statement decision |
| `thm_13_2` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | proof/statement decision |
| `thm_13_4` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `thm_13_6` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |
| `thm_13_7` | `proved_body_reassumption_not_passed`:5, `proved_contract_not_verified`:5, `proved_missing_expected_signature`:5, `proved_public_premise_not_passed`:5, `proved_signature_not_passed`:5 | metadata review |
| `thm_13_8` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |
| `thm_13_9` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | metadata review |
| `thm_14_1` | `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | proof/statement decision |
| `thm_14_2` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | proof/statement decision |
| `thm_14_4` | `landing_not_found_in_output`:2, `proved_body_reassumption_not_passed`:3, `proved_contract_not_verified`:3, `proved_forbidden_landing_kind`:2, `proved_missing_expected_signature`:3, `proved_public_premise_not_passed`:3, `proved_signature_not_passed`:3 | proof/statement decision |
| `thm_14_6` | `proved_body_reassumption_not_passed`:8, `proved_contract_not_verified`:8, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:8, `proved_public_premise_not_passed`:8, `proved_signature_not_passed`:8 | proof/statement decision |
| `thm_14_7` | `open_missing_expected_signature`:3, `proved_body_reassumption_not_passed`:2, `proved_contract_not_verified`:2, `proved_forbidden_landing_kind`:1, `proved_missing_expected_signature`:2, `proved_public_premise_not_passed`:2, `proved_signature_not_passed`:2 | proof/statement decision |
| `thm_9_5` | `landing_not_found_in_output`:4, `proved_body_reassumption_not_passed`:7, `proved_contract_not_verified`:7, `proved_forbidden_landing_kind`:4, `proved_missing_expected_signature`:7, `proved_public_premise_not_passed`:7, `proved_signature_not_passed`:7 | proof/statement decision |
| `thm_9_6` | `proved_body_reassumption_not_passed`:4, `proved_contract_not_verified`:4, `proved_missing_expected_signature`:4, `proved_public_premise_not_passed`:4, `proved_signature_not_passed`:4 | metadata review |

## Verification Expectations

Required commands after this reconciliation:

```powershell
python -m py_compile tools/validate_phase2_obligation_contracts.py tools/validate_phase2_completion_classification.py
python -m unittest tests.test_phase2_obligation_contracts tests.test_phase2_completion_classification tests.test_phase2_proof_obligations tests.test_phase2_review_apply tests.test_phase2_pack_generation
python tools/validate_phase2_completion_classification.py
python tools/validate_phase2_completion_classification.py --require-proof-contract
python tools/validate_phase2_obligation_contracts.py --write-report
```

Global contract errors remaining after these commands are not waived; they are the explicit queue for later reconciliation or proof-route work.
