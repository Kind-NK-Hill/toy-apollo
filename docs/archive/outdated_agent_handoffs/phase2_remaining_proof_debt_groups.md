# Phase 2 Remaining Proof-Debt Groups

## Current Status Update

This file is now a historical grouping note. Its original count below is from
2026-05-19 and is no longer the current source of truth.

As of 2026-05-20 after Batches 1 through 6:

- no parent task currently has
  `proof_obligation_summary.status_counts.accepted_as_proof_debt > 0`;
- the Chapter 14 parent tasks listed below have been reconciled to
  `COMPLETED`;
- the next useful "remaining batch" is ledger hygiene, described in
  `docs/proof_debt_remaining_batch_handoff.md`.

Do not restart from the `77 accepted proof-debt obligations` count below unless
you first re-run a fresh ledger audit and prove that the current worktree has
regressed.

Snapshot date: 2026-05-19.

Source of truth checked:

- `python .\run_chapter.py --status`
- every `phase2_prompt_packs/*/proof_obligations.json` entry whose status is
  `accepted_as_proof_debt`

Current total: 77 accepted proof-debt obligations across 35 tasks.

## A. Skorokhod, Quantile, And CDF-To-Weak Bridges

Count: 5.

These should be treated as one shared real-line distribution-convergence
foundation, not theorem-local bridges.

- `thm_10_8.quantile_law_preservation`: quantile law preservation.
- `thm_10_8.upper_lower_inverse_comparison`: lower/upper generalized inverse comparison.
- `thm_10_8.almost_sure_quantile_convergence`: almost-sure convergence of the coupled quantiles.
- `thm_14_2.distribution_to_weak`: CDF convergence implies weak convergence.
- `prob_14_1.obligation_5`: CDF convergence to weak convergence.

## B. Characteristic-Function, Levy, MGF, And Slutsky Bridges

Count: 17.

These are mostly interface/foundation debts around characteristic functions,
weak convergence, MGF conversion, subsequences, and perturbation stability.

- `prob_10_10.constant_distribution_to_probability`: constant distribution convergence to probability convergence.
- `prob_10_10.distribution_stability_under_probability_perturbation`: Slutsky perturbation stability.
- `prob_14_3.obligation_4`: tightness-to-weak direction through Levy.
- `prob_14_6.obligation_3`: convergence in probability to weak convergence.
- `prob_14_7.obligation_1`: distribution convergence to characteristic convergence.
- `prob_14_7.obligation_2`: independence gives sum characteristic product.
- `prob_14_7.obligation_3`: target sum characteristic product.
- `prob_14_8.obligation_4`: MGF to characteristic convergence.
- `prob_14_9.obligation_3`: pushforward law representation.
- `prob_14_9.obligation_4`: Levy characteristic convergence for mapped laws.
- `prob_14_10.obligation_3`: weak convergence to moment convergence on compact support.
- `prob_14_10.obligation_4`: moments to MGF convergence.
- `thm_14_6.theorem_14_3_characteristic_limit`: Theorem 14.3 gives characteristic convergence.
- `thm_14_6.subsequence_characteristic_limit`: characteristic limit passes to subsequences.
- `thm_14_6.inversion_formula_identification`: Theorem 9.5 identifies the limiting law.
- `thm_14_6.subsubsequence_test_integral_limit`: test-integral subsequence/subsubsequence bridge.
- `thm_14_6.real_analysis_subsequence_principle`: numerical subsequence principle.

## C. Total Variation, Radon-Nikodym, And Density Formula Bridges

Count: 7.

These are density/TV identity debts. They should reuse and generalize existing
`tv_distance_core`, `thm_8_6`, and `thm_14_4_dominating_measure` work.

- `ex_10_3_2.gaussian_density_special_case`: Gaussian density convergence and distribution convergence.
- `prob_11_4.density_mean_interface`: density interface gives mean value.
- `prob_14_5.obligation_3`: TV bounded-test squeeze estimate.
- `prob_14_5.obligation_4`: discrete singleton indicators as bounded continuous tests.
- `prob_14_5.obligation_5`: discrete countable summation to total variation.
- `thm_14_4.triangle_density_bound`: RN triangle density estimate.
- `thm_14_4.adapted_theorem_8_6_identity`: adapt Theorem 8.6 to arbitrary dominating probability measure.

## D. Measure-Theoretic Extension, Fubini, Conditional Expectation, And DCT

Count: 7.

These are not one-line interface debts. They require measure-theoretic
extension arguments, conditional-expectation verification, or DCT assembly.

- `ex_13_5_1.rectangle_area`: compute integrals on rectangles `[a,b] x [0,1]`.
- `ex_13_5_1.pi_lambda_extension`: extend rectangle result to all `C x [0,1]`.
- `thm_13_12.candidate_satisfies_def_13_3`: conditional expectation verification via sigma-field extension.
- `thm_13_14.interval_fubini_calculation`: Fubini computation on closed-interval cylinders.
- `thm_13_14.pi_lambda_extension`: extend closed intervals to all Borel y-sets.
- `thm_13_18.uniform_bound_case`: bounded martingale plus DCT.
- `thm_13_18.bounded_increment_case`: bounded increments, telescoping domination, plus DCT.

## E. Moment, Tail, Uniform-Integrability, LLN, And Tightness Estimates

Count: 12.

These should be grouped by reusable inequality and summability lemmas, especially
Chapter 11 moment/tail estimates and Chapter 14 tightness/UI estimates.

- `prob_11_5.tail_summability_support`: summable tail comparison.
- `prob_11_6.sixth_moment_support`: sixth-moment estimate.
- `prob_11_6.tail_summability_support`: Markov and p-series comparison.
- `prob_11_7.variance_decay_support`: covariance-band variance decay.
- `prob_11_8.covariance_decay_support`: geometric covariance-decay calculation.
- `prob_11_10.continuous_grid_uniformization`: finite-grid uniformization argument.
- `thm_11_7.fourth_moment_expansion_tail_bound`: fourth-moment SLLN tail bound.
- `prob_14_6.obligation_1`: scaling constants and tail-probability convergence.
- `prob_14_8.obligation_3`: MGF to tightness.
- `prob_14_12.obligation_2`: variable UI to law UI.
- `prob_14_12.obligation_3`: Markov tail argument from UI to tightness.
- `prob_14_12.obligation_5`: UI plus convergence in probability implies convergence in mean.

## F. Theorem 14.5 Tightness Kernel Spine

Count: 10.

This is one large source-spine proof and should be handled as a dedicated
foundation, not as ten independent theorem-local supports.

- `thm_14_5.characteristic_at_zero`: characteristic functions give `c(0)=1`.
- `thm_14_5.fubini_identity`: Fubini identity (14.3).
- `thm_14_5.inner_integral_identity`: inner integral computation (14.4).
- `thm_14_5.averaged_kernel_identity`: combine (14.3) and (14.4) into (14.5).
- `thm_14_5.kernel_tail_lower_bound`: kernel lower bound on the tail.
- `thm_14_5.tail_bound_by_averaged_characteristic`: tail probability bound (14.6).
- `thm_14_5.continuity_small_u_bound`: small-window estimate from continuity at zero.
- `thm_14_5.dominated_convergence_bound`: DCT for `c(t)-phi_n(t)`.
- `thm_14_5.finite_prefix_tail_bound`: handle finitely many early indices.
- `thm_14_5.uniform_tail_bound`: assemble the uniform tail bound.

## G. Explicit Distribution, Combinatorial, And Asymptotic Calculations

Count: 9.

These are concrete model calculations: Polya urns, occupancy, Gaussian
asymptotics, Gamma sums, or waiting-time equations.

- `ex_13_6_5.expected_waiting_times`: solve the two ABRACADABRA expectation equations.
- `prob_11_9.occupancy_moment_calculation`: balls-in-boxes second-moment calculation.
- `prob_14_1.obligation_1`: finite Polya urn count formula.
- `prob_14_1.obligation_2`: scaled white fraction law.
- `prob_14_1.obligation_3`: Beta law interface.
- `prob_14_1.obligation_4`: Stirling to Beta CDF convergence.
- `prob_14_2.gamma_sum_representation`: represent Gamma as iid Gamma sum.
- `prob_14_3.obligation_2`: Gaussian `N(0,n)` characteristic-function limit.
- `prob_14_4.obligation_2`: shrinking Gaussian characteristic-function limit.

## H. CLT, Triangular Array, And Normal Approximation Foundations

Count: 8.

These are shared CLT foundations and should reuse Chapter 9 characteristic
function output plus Chapter 14 triangular-array structures.

- `ex_14_4_3.lyapunov_fourth_moment_bound`: Lyapunov delta=2 verification by fourth moments.
- `prob_14_11.obligation_2`: generalized triangular array.
- `prob_14_11.obligation_3`: generalized mean and variance scales.
- `prob_14_11.obligation_4`: generalized Lyapunov verification.
- `thm_14_7.center_and_standardize`: center and standardize the iid sequence.
- `thm_14_7.quadratic_characteristic_expansion`: quadratic one-step characteristic expansion.
- `thm_14_7.independent_sum_characteristic`: independence gives product characteristic function.
- `thm_14_8.beyond_book_proof_obligations`: external triangular-array CLT obligations.

## I. Small Local Interface Or Downstream Application Debt

Count: 2.

These do not obviously need a new large foundation. They should be tried as
small local repairs after checking current downstream APIs.

- `ex_13_6_5.optional_stopping_zero_gain`: apply Theorem 13.18 to the gambling-team martingale.
- `prob_14_6.obligation_2`: measurability needed for the scaled variables.

## Count Check

`5 + 17 + 7 + 7 + 12 + 10 + 9 + 8 + 2 = 77`.
