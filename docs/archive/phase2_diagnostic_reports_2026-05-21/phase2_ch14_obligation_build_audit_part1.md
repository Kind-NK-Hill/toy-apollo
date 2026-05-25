# Phase2 Unfinished Task Audit

- Generated at: `2026-05-22T00:34:53.826948Z`
- Scope: chapters `9`-`14`
- Extra included tasks: `thm_6_7__lemma_1`
- Task filter: `prob_14_1, prob_14_10, prob_14_8`
- Bucket filter: `(none)`
- Build checked: `True`
- Build timeout seconds: `240`
- Unfinished or verify count: `3`
- Blocking unfinished count: `3`
- Verification-only count: `0`
- Orphan output count: `10`

## Reason Counts

- `ledger_status:FAILED_LOCAL`: 3
- `open_obligations`: 3

## Open Obligation Kinds

- `proof_debt_support`: 4
- `interface-name matches`: 0
- `structure-field landings`: 4
- `theorem wrappers over structure fields`: 3
- `empty landings`: 0
- `ledger-only child obligations`: 4

## Build Status Counts

- `ok`: 3

## Repair Batches

- `obligation_resolution` (3): `prob_14_1, prob_14_10, prob_14_8`
  - action: Resolve the open proof obligations and land them on theorem/lemma declarations rather than structure fields.

## Tasks

- `prob_14_1` ch14 `FAILED_LOCAL` `ToyApollo/Output/prob_14_1.lean` `obligation_resolution`: `ledger_status:FAILED_LOCAL`, `open_obligations`
  - open: `obligation_1, obligation_4`
  - obligation `obligation_1` `proof_debt_support`: status `open`, landing `prob_14_1_PolyaUrnBetaSetup.polya_white_count_mass / prob_14_1_white_count_mass`, landing problem `theorem_wrapper_over_structure_field`, child `obl_prob_14_1_obligation_1` `FAILED_LOCAL` output `False`
  - obligation `obligation_4` `proof_debt_support`: status `open`, landing `prob_14_1_PolyaUrnBetaSetup.stirling_cdf_convergence / prob_14_1_stirling_beta_cdf_convergence`, landing problem `theorem_wrapper_over_structure_field`, child `obl_prob_14_1_obligation_4` `FAILED_LOCAL` output `False`
  - build: `ok`
- `prob_14_10` ch14 `FAILED_LOCAL` `ToyApollo/Output/prob_14_10.lean` `obligation_resolution`: `ledger_status:FAILED_LOCAL`, `open_obligations`
  - open: `obligation_4`
  - obligation `obligation_4` `proof_debt_support`: status `open`, landing `prob_14_10_BoundedMomentSetup.moments_to_mgf_setup`, landing problem `structure_field_landing`, child `obl_prob_14_10_obligation_4` `FAILED_LOCAL` output `False`
  - build: `ok`
- `prob_14_8` ch14 `FAILED_LOCAL` `ToyApollo/Output/prob_14_8.lean` `obligation_resolution`: `ledger_status:FAILED_LOCAL`, `open_obligations`
  - open: `obligation_4`
  - obligation `obligation_4` `proof_debt_support`: status `open`, landing `prob_14_8_MgfConvergenceSetup.mgf_to_characteristic_convergence / prob_14_8_characteristic_convergence`, landing problem `theorem_wrapper_over_structure_field`, child `obl_prob_14_8_obligation_4` `FAILED_LOCAL` output `False`
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
