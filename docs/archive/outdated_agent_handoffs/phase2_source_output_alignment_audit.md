# Phase 2 Source-Output Alignment Audit

Snapshot date: 2026-05-19.

Purpose: convert every accepted proof-debt gap into one of four concrete actions: import an existing theorem, write a narrow interface translation, formalize the source proof step locally, or keep only a verified external/foundation gap.

## Classification Rules

- `A_existing_theorem_candidate`: all recorded landing names resolve to theorem/lemma declarations. These are the first candidates for import/rewrite and debt retirement, but their hypotheses still need review.
- `B_partial_theorem_plus_support_interface`: at least one theorem/lemma exists, but the landing also contains definitions or structures. Use the theorem part, then formalize the remaining source step.
- `B_partial_theorem_plus_missing_or_support`: at least one theorem/lemma exists, but another recorded landing name is missing, usually a support assumption or structure field. This is not clean until the missing part is replaced.
- `C_support_predicate_or_structure_only`: the recorded landing is only a support predicate, structure, definition, or field. This is not a cleared proof; replace it by theorem-level evidence.
- `D_no_landing_search_required` / `D_landing_names_missing`: no usable local landing is recorded or found. Re-open source/output search before accepting it as real debt.

## Counts

- Total accepted debt items: 77
- A_existing_theorem_candidate: 2
- B_partial_theorem_plus_missing_or_support: 2
- B_partial_theorem_plus_support_interface: 5
- C_support_field_gap_no_decl: 28
- C_support_predicate_or_structure_only: 5
- D_no_landing_search_required: 35

## Family Counts

- cdf/weak/law: 6
- characteristic/levy/mgf: 16
- clt/triangular: 3
- martingale/stopping: 1
- measure/fubini/dct: 8
- other: 14
- quantile/skorokhod: 4
- tail/moment/ui: 19
- tv/rn/density: 6

## Manual Follow-up Notes

- `ex_13_6_5.optional_stopping_zero_gain` and `ex_13_6_5.expected_waiting_times` have theorem landings, but signature inspection shows they still carry model-specific hypotheses such as `hThirdCase`, `hInitialGainZero`, and terminal payoff integral identities. Treat them as interface/source-formalization work, not clean debt retirement.
- `prob_10_10.constant_distribution_to_probability` can import `prob_10_3`, but `prob_10_3` itself still requires `h_constant_bridge`; this is a partial source-output alignment, not a completed proof.
- `thm_10_8.quantile_law_preservation` already has the CDF-to-law bridge in `thm_10_8_quantile_law.lean`; the remaining work is the source event calculation and measurability needed to feed that bridge.

## Audit Table

| task.obligation | family | classification | existing local declarations | missing landing names | next action |
| --- | --- | --- | --- | --- | --- |
| `ex_10_3_2.gaussian_density_special_case` | tv/rn/density | `B_partial_theorem_plus_support_interface` | `ex_10_3_2_gaussianPdf` (def, `ToyApollo/Output/ex_10_3_2.lean:197`)<br>`ex_10_3_2_GaussianDensityConvergenceSetup` (structure, `ToyApollo/Output/ex_10_3_2.lean:205`)<br>`ex_10_3_2_gaussian_convergesInDistribution` (theorem, `ToyApollo/Output/ex_10_3_2.lean:238`) | - | Use the existing theorem part, then replace the remaining support interface with source-aligned local lemmas. |
| `ex_13_5_1.pi_lambda_extension` | measure/fubini/dct | `C_support_predicate_or_structure_only` | `ex_13_5_1_xCylinder` (def, `ToyApollo/Output/ex_13_5_1.lean:132`)<br>`ex_13_5_1_sigmaXMeasurableSet` (def, `ToyApollo/Output/ex_13_5_1.lean:141`)<br>`ex_13_5_1_piLambdaExtensionSupport` (def, `ToyApollo/Output/ex_13_5_1.lean:178`) | - | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `ex_13_5_1.rectangle_area` | measure/fubini/dct | `C_support_predicate_or_structure_only` | `ex_13_5_1_rectangle` (def, `ToyApollo/Output/ex_13_5_1.lean:136`)<br>`ex_13_5_1_rectangleAreaSupport` (def, `ToyApollo/Output/ex_13_5_1.lean:158`) | - | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `ex_13_6_5.expected_waiting_times` | other | `A_existing_theorem_candidate` | `ex_13_6_5_abab_expectedWaitingTime` (theorem, `ToyApollo/Output/ex_13_6_5.lean:190`)<br>`ex_13_6_5_aabb_expectedWaitingTime` (theorem, `ToyApollo/Output/ex_13_6_5.lean:209`)<br>`ex_13_6_5_aabb_shorter_than_abab` (theorem, `ToyApollo/Output/ex_13_6_5.lean:229`)<br>`ex_13_6_5` (theorem, `ToyApollo/Output/ex_13_6_5.lean:254`) | - | Check theorem hypotheses; retire the debt only if the declaration does not carry an equivalent support assumption. |
| `ex_13_6_5.optional_stopping_zero_gain` | martingale/stopping | `A_existing_theorem_candidate` | `ex_13_6_5_teamGain_zero_from_optionalStopping` (theorem, `ToyApollo/Output/ex_13_6_5.lean:171`) | - | Check theorem hypotheses; retire the debt only if the declaration does not carry an equivalent support assumption. |
| `ex_14_4_3.lyapunov_fourth_moment_bound` | tail/moment/ui | `C_support_predicate_or_structure_only` | `ex_14_4_3_LyapunovVerification` (structure, `ToyApollo/Output/ex_14_4_3.lean:348`) | - | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `prob_10_10.constant_distribution_to_probability` | cdf/weak/law | `B_partial_theorem_plus_missing_or_support` | `prob_10_3` (theorem, `ToyApollo/Output/prob_10_3.lean:20`) | `h_constant_support` | Use the existing theorem part; split or replace each missing support landing with a source lemma or interface translation. |
| `prob_10_10.distribution_stability_under_probability_perturbation` | cdf/weak/law | `C_support_field_gap_no_decl` | - | `h_add_perturbation_support`, `h_mul_perturbation_support` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `prob_11_10.continuous_grid_uniformization` | tail/moment/ui | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_11_4.density_mean_interface` | tv/rn/density | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_11_5.tail_summability_support` | tail/moment/ui | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_11_6.sixth_moment_support` | tail/moment/ui | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_11_6.tail_summability_support` | tail/moment/ui | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_11_7.variance_decay_support` | tail/moment/ui | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_11_8.covariance_decay_support` | tail/moment/ui | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_11_9.occupancy_moment_calculation` | tail/moment/ui | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_1.obligation_1` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_1.obligation_2` | cdf/weak/law | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_1.obligation_3` | tv/rn/density | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_1.obligation_4` | cdf/weak/law | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_1.obligation_5` | cdf/weak/law | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_10.obligation_3` | tail/moment/ui | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_10.obligation_4` | characteristic/levy/mgf | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_11.obligation_2` | clt/triangular | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_11.obligation_3` | tail/moment/ui | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_11.obligation_4` | clt/triangular | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_12.obligation_2` | tail/moment/ui | `C_support_field_gap_no_decl` | - | `prob_14_12_TightnessSetup.variable_ui_to_law_ui'` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `prob_14_12.obligation_3` | tail/moment/ui | `C_support_field_gap_no_decl` | - | `prob_14_12_TightnessSetup.markov_tail_uniform_integrability_to_tightness'`, `prob_14_12_uniformIntegrable_tight'` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `prob_14_12.obligation_5` | tail/moment/ui | `C_support_field_gap_no_decl` | - | `prob_14_12_MeanConvergenceSetup.uniform_integrability_probability_to_mean'`, `prob_14_12_uniformIntegrable_probability_to_mean'` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `prob_14_2.gamma_sum_representation` | characteristic/levy/mgf | `B_partial_theorem_plus_missing_or_support` | `prob_14_2_gammaScaleCharacteristic` (def, `ToyApollo/Output/prob_14_2.lean:55`)<br>`prob_14_2_iidGammaSumRepresentation` (def, `ToyApollo/Output/prob_14_2.lean:68`)<br>`prob_14_2_gamma_pair_sum_density` (theorem, `ToyApollo/Output/prob_14_2.lean:91`) | `prob_14_2_GammaCLTSetup.gamma_as_iid_sum` | Use the existing theorem part; split or replace each missing support landing with a source lemma or interface translation. |
| `prob_14_3.obligation_2` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_3.obligation_4` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_4.obligation_2` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_5.obligation_3` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_5.obligation_4` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_5.obligation_5` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_6.obligation_1` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_6.obligation_2` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_6.obligation_3` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_7.obligation_1` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_7.obligation_2` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_7.obligation_3` | other | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_8.obligation_3` | characteristic/levy/mgf | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_8.obligation_4` | characteristic/levy/mgf | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_9.obligation_3` | cdf/weak/law | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `prob_14_9.obligation_4` | characteristic/levy/mgf | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `thm_10_8.almost_sure_quantile_convergence` | quantile/skorokhod | `C_support_field_gap_no_decl` | - | `SkorokhodQuantileSupport.almost_sure_quantile_convergence` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_10_8.quantile_event_measurability` | quantile/skorokhod | `C_support_field_gap_no_decl` | - | `SkorokhodQuantileSupport.Yn_measurable`, `SkorokhodQuantileSupport.Y_measurable`, `SkorokhodQuantileSupport.Yn_Iic`, `SkorokhodQuantileSupport.Y_Iic` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_10_8.upper_lower_inverse_comparison` | quantile/skorokhod | `C_support_field_gap_no_decl` | - | `SkorokhodQuantileSupport.upper_lower_inverse_comparison` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_11_7.fourth_moment_expansion_tail_bound` | tail/moment/ui | `C_support_field_gap_no_decl` | `thm_11_7_tailSummabilitySupport` (def, `ToyApollo/Output/thm_11_7.lean:228`) | `h_tail_summability_support` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_13_12.candidate_satisfies_def_13_3` | measure/fubini/dct | `D_no_landing_search_required` | - | - | Re-open the source and ToyApollo/Output search, then assign a real Lean landing before repair. |
| `thm_13_14.interval_fubini_calculation` | tv/rn/density | `C_support_predicate_or_structure_only` | `thm_13_14_closedIntervalCylinder` (def, `ToyApollo/Output/thm_13_14.lean:261`)<br>`thm_13_14_intervalFubiniSupport` (def, `ToyApollo/Output/thm_13_14.lean:277`) | - | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_13_14.pi_lambda_extension` | measure/fubini/dct | `C_support_predicate_or_structure_only` | `thm_13_14_verticalCylinder` (def, `ToyApollo/Output/thm_13_14.lean:256`)<br>`thm_13_14_sigmaYMeasurableSet` (def, `ToyApollo/Output/thm_13_14.lean:266`)<br>`thm_13_14_piLambdaExtensionSupport` (def, `ToyApollo/Output/thm_13_14.lean:286`) | - | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_13_18.bounded_increment_case` | measure/fubini/dct | `B_partial_theorem_plus_support_interface` | `thm_13_18_boundedIncrementCase` (def, `ToyApollo/Output/thm_13_18.lean:173`)<br>`thm_13_18_boundedIncrementCaseCanonical` (def, `ToyApollo/Output/thm_13_18.lean:217`)<br>`thm_13_18_boundedIncrementCase_of_canonical` (theorem, `ToyApollo/Output/thm_13_18.lean:260`)<br>`thm_13_18_boundedIncrement_case` (theorem, `ToyApollo/Output/thm_13_18.lean:361`) | - | Use the existing theorem part, then replace the remaining support interface with source-aligned local lemmas. |
| `thm_13_18.uniform_bound_case` | tail/moment/ui | `B_partial_theorem_plus_support_interface` | `thm_13_18_uniformBoundCase` (def, `ToyApollo/Output/thm_13_18.lean:158`)<br>`thm_13_18_uniformBoundCaseCanonical` (def, `ToyApollo/Output/thm_13_18.lean:205`)<br>`thm_13_18_uniformBoundCase_of_canonical` (theorem, `ToyApollo/Output/thm_13_18.lean:250`)<br>`thm_13_18_uniformBound_case` (theorem, `ToyApollo/Output/thm_13_18.lean:350`) | - | Use the existing theorem part, then replace the remaining support interface with source-aligned local lemmas. |
| `thm_14_2.distribution_to_weak` | quantile/skorokhod | `B_partial_theorem_plus_support_interface` | `thm_14_2_DistributionToWeakSupport` (structure, `ToyApollo/Output/thm_14_2.lean:214`)<br>`thm_14_2_skorokhod_representation` (theorem, `ToyApollo/Output/thm_14_2.lean:226`) | - | Use the existing theorem part, then replace the remaining support interface with source-aligned local lemmas. |
| `thm_14_4.adapted_theorem_8_6_identity` | tv/rn/density | `C_support_field_gap_no_decl` | - | `thm_14_4_RadonNikodymTotalVariationSupport.adapted_theorem_8_6_identity` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_4.triangle_density_bound` | tv/rn/density | `C_support_field_gap_no_decl` | - | `thm_14_4_RadonNikodymTotalVariationSupport.triangle_density_bound` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_5.averaged_kernel_identity` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | - | `thm_14_5_SourceProofSpine.averaged_kernel_identity` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_5.characteristic_at_zero` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | - | `thm_14_5_SourceProofSpine.characteristic_at_zero` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_5.continuity_small_u_bound` | measure/fubini/dct | `C_support_field_gap_no_decl` | - | `thm_14_5_SourceProofSpine.continuity_small_u_bound` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_5.dominated_convergence_bound` | tail/moment/ui | `C_support_field_gap_no_decl` | - | `thm_14_5_SourceProofSpine.dominated_convergence_bound` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_5.finite_prefix_tail_bound` | tail/moment/ui | `C_support_field_gap_no_decl` | - | `thm_14_5_SourceProofSpine.finite_prefix_tail_bound` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_5.fubini_identity` | measure/fubini/dct | `C_support_field_gap_no_decl` | - | `thm_14_5_SourceProofSpine.fubini_identity` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_5.inner_integral_identity` | measure/fubini/dct | `C_support_field_gap_no_decl` | - | `thm_14_5_SourceProofSpine.inner_integral_identity` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_5.kernel_tail_lower_bound` | tail/moment/ui | `C_support_field_gap_no_decl` | - | `thm_14_5_SourceProofSpine.kernel_tail_lower_bound` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_5.tail_bound_by_averaged_characteristic` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | - | `thm_14_5_SourceProofSpine.tail_bound_by_averaged_characteristic` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_5.uniform_tail_bound` | tail/moment/ui | `C_support_field_gap_no_decl` | - | `thm_14_5_SourceProofSpine.uniform_tail_bound` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_6.inversion_formula_identification` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | - | `thm_14_6_LevyCompletionSpine.inversion_formula_identifies_limit` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_6.real_analysis_subsequence_principle` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | - | `thm_14_6_LevyCompletionSpine.real_analysis_subsequence_principle` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_6.subsequence_characteristic_limit` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | - | `thm_14_6_LevyCompletionSpine.subsequence_inherits_characteristic_limit` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_6.subsubsequence_test_integral_limit` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | `thm_14_6_everySubsequenceHasSubsubsequenceLimit` (def, `ToyApollo/Output/thm_14_6.lean:231`) | `thm_14_6_LevyCompletionSpine.subsubsequence_test_integral_limit` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_6.theorem_14_3_characteristic_limit` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | - | `thm_14_6_LevyCompletionSpine.theorem_14_3_characteristic_limit` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_7.center_and_standardize` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | - | `thm_14_7_LindebergLevySetup.mean`, `thm_14_7_LindebergLevySetup.sigma`, `thm_14_7_LindebergLevySetup.standardizedLaws` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_7.independent_sum_characteristic` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | - | `thm_14_7_LindebergLevySetup.c`, `thm_14_7_LindebergLevySetup.c_definition` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_7.quadratic_characteristic_expansion` | characteristic/levy/mgf | `C_support_field_gap_no_decl` | `thm_14_7_quadraticCharacteristicExpansion` (def, `ToyApollo/Output/thm_14_7.lean:148`) | `thm_14_7_LindebergLevySetup.quadratic_expansion` | Do not count this as proof; replace the support predicate, structure, or field with theorem-level evidence. |
| `thm_14_8.beyond_book_proof_obligations` | clt/triangular | `B_partial_theorem_plus_support_interface` | `thm_14_8_ProofBeyondBook` (structure, `ToyApollo/Output/thm_14_8.lean:167`)<br>`thm_14_8_of_lindeberg` (theorem, `ToyApollo/Output/thm_14_8.lean:175`)<br>`thm_14_8_of_lyapunov` (theorem, `ToyApollo/Output/thm_14_8.lean:184`)<br>`thm_14_8` (theorem, `ToyApollo/Output/thm_14_8.lean:195`) | - | Use the existing theorem part, then replace the remaining support interface with source-aligned local lemmas. |

## Immediate Queue

Start with `A_existing_theorem_candidate` and both `B_partial_*` classes, but do not mark any item proved merely because a symbol exists. The declaration must actually discharge the source obligation without carrying an equivalent support assumption.

This audit is also attached back to each accepted debt item as `source_output_alignment`, so debt-fix prompts can act on every existing gap rather than rediscovering this classification manually.
