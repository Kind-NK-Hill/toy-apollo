# Phase2 Step 8 `thm_11_7` Completion Report

task_id: thm_11_7

result: textbook_proof_completed

files_touched:

- `ToyApollo/Output/thm_11_7.lean`
- `phase2_prompt_packs/thm_11_7/proof_obligations.json`
- `docs/phase2_completion_classification.json`
- `docs/phase2_completion_classification.md`
- `docs/modification_0525_steps/phase2_step7_thm_11_7_bridge_foundation_report.md`
- `docs/modification_0525_steps/phase2_step8_thm_11_7_completion_report.md`

Lean declarations landed:

- `thm_11_7_centeredFourthMomentUniformBound`
- `thm_11_7_fourth_centering_pointwise_bound`
- `thm_11_7_centeredFourthMomentUniformBound_of_fourthMomentUniformBound`
- `thm_11_7_fourth_moment_sum_bound`
- `thm_11_7_tail_summability_from_fourth_moment`
- public `thm_11_7` with no `h_tail_summability` premise

Proof route:

1. `thm_11_7_fourthMomentUniformBound` records the uncentered textbook source
   assumption. The centered `L^4`/moment package is derived internally by
   `thm_11_7_centeredFourthMomentUniformBound_of_fourthMomentUniformBound`,
   using `(x - μ)^4 <= 8 * (x^4 + μ^4)`.
2. `thm_11_7_fourth_moment_sum_bound` proves the finite partial-sum fourth-moment
   estimate by expanding the fourth power, cancelling singleton mixed terms,
   bounding paired-square terms by the uniform fourth moment, and counting the
   three pairing patterns.
3. `thm_11_7_tail_summability_from_fourth_moment` feeds that estimate through
   the existing Markov, ratio, and p-series bridge.
4. public `thm_11_7` calls the internal tail-summability theorem and then uses
   the already landed Borel-Cantelli / Theorem 10.1 assembly.

Obligation/classification changes:

- `fourth_moment_expansion_tail_bound`: `proved`, `proof_contract_status:
  verified`, `signature_match/body_reassumption_check/public_premise_check:
  passed`.
- `borel_cantelli_limsup_step`: `proved`.
- `almost_sure_convergence_bridge`: `proved`.
- `docs/phase2_completion_classification.json`: `thm_11_7` promoted to
  `textbook_proof_completed`.

Validation:

- `lake env lean ToyApollo/Output/thm_11_7.lean`: passed.
- `python tools/validate_phase2_obligation_contracts.py --task thm_11_7`:
  `0 error / 0 warning`.
- `python tools/validate_phase2_completion_classification.py`: passed.
- `python tools/validate_phase2_completion_classification.py --require-proof-contract`:
  passed.
- `python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors`:
  `error_task_count: 0`.
- `python -m unittest tests.test_phase2_completion_classification tests.test_phase2_clean_debt_surface_audit`:
  `Ran 19 tests`, `OK`.

Remaining `thm_11_7` debt: none.

## Self-Correction Addendum

2026-05-26 review found one hidden-strengthening risk in the previous report:
the public `thm_11_7_fourthMomentUniformBound` package directly required
centered `MemLp (fun ω => X i ω - μ) 4 P` and centered fourth-moment bounds.
That was stronger than the textbook statement `E[X_i^4] <= c < infinity`.

The Lean file was repaired instead of downgrading:

- public `thm_11_7_fourthMomentUniformBound` now uses uncentered `X i`;
- the centered package is internal-only as `thm_11_7_centeredFourthMomentUniformBound`;
- `thm_11_7_centeredFourthMomentUniformBound_of_fourthMomentUniformBound`
  proves the bridge from the source assumption to the centered package;
- public `thm_11_7` still has no `h_tail_summability` or equivalent proof
  package premise.
