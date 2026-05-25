# Phase2 Unfinished Task Audit

- Generated at: `2026-05-22T00:29:54.734242Z`
- Scope: chapters `9`-`14`
- Extra included tasks: `thm_6_7__lemma_1`
- Task filter: `ex_14_4_3, thm_13_14`
- Bucket filter: `(none)`
- Build checked: `True`
- Unfinished or verify count: `2`
- Blocking unfinished count: `2`
- Verification-only count: `0`
- Orphan output count: `10`

## Reason Counts

- `ledger_status:FAILED_LOCAL`: 2
- `open_obligations`: 2
- `public_surface_error`: 2

## Open Obligation Kinds

- `proof_debt_support`: 3
- `interface-name matches`: 0
- `structure-field landings`: 0
- `theorem wrappers over structure fields`: 0
- `empty landings`: 0
- `ledger-only child obligations`: 3

## Build Status Counts

- `ok`: 2

## Repair Batches

- `public_surface_and_obligations` (2): `thm_13_14, ex_14_4_3`
  - action: First remove public Support/Spine parameters, then close the named proof obligations with theorem-level landings.

## Tasks

- `thm_13_14` ch13 `FAILED_LOCAL` `ToyApollo/Output/thm_13_14.lean` `public_surface_and_obligations`: `ledger_status:FAILED_LOCAL`, `open_obligations`, `public_surface_error`
  - open: `interval_fubini_calculation, pi_lambda_extension`
  - obligation `interval_fubini_calculation` `proof_debt_support`: status `open`, landing `thm_13_14_closedIntervalCylinder_eq_prod`, child `obl_thm_13_14_interval_fubini_calculation` `FAILED_LOCAL` output `False`
  - obligation `pi_lambda_extension` `proof_debt_support`: status `open`, landing `thm_13_14_verticalCylinder_eq_prod`, child `obl_thm_13_14_pi_lambda_extension` `FAILED_LOCAL` output `False`
- `ex_14_4_3` ch14 `FAILED_LOCAL` `ToyApollo/Output/ex_14_4_3.lean` `public_surface_and_obligations`: `ledger_status:FAILED_LOCAL`, `open_obligations`, `public_surface_error`
  - open: `lyapunov_fourth_moment_bound`
  - obligation `lyapunov_fourth_moment_bound` `proof_debt_support`: status `open`, landing `ex_14_4_3_LyapunovVerification`, landing problem `non_theorem_landing`, child `obl_ex_14_4_3_lyapunov_fourth_moment_bound` `FAILED_LOCAL` output `False`

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
