# Phase2 Unfinished Task Audit

- Generated at: `2026-05-22T00:32:28.407271Z`
- Scope: chapters `9`-`14`
- Extra included tasks: `thm_6_7__lemma_1`
- Task filter: `prob_11_10, prob_11_6, prob_11_8, prob_11_9, thm_11_7`
- Bucket filter: `(none)`
- Build checked: `True`
- Unfinished or verify count: `5`
- Blocking unfinished count: `5`
- Verification-only count: `0`
- Orphan output count: `10`

## Reason Counts

- `ledger_status:FAILED_LOCAL`: 5
- `open_obligations`: 5
- `public_surface_error`: 5

## Open Obligation Kinds

- `proof_debt_support`: 5
- `interface-name matches`: 0
- `structure-field landings`: 0
- `theorem wrappers over structure fields`: 0
- `empty landings`: 5
- `ledger-only child obligations`: 5

## Build Status Counts

- `ok`: 5

## Repair Batches

- `public_surface_and_obligations` (5): `prob_11_10, prob_11_6, prob_11_8, prob_11_9, thm_11_7`
  - action: First remove public Support/Spine parameters, then close the named proof obligations with theorem-level landings.

## Tasks

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
