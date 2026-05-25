# Phase2 Completion Classification

Created: 2026-05-24
Status: ledger-independent classification

## Purpose

This document separates mathematical completion fidelity from execution ledger status. A Lean build, clean public-surface audit, or completed ledger item is not by itself a claim that the textbook proof route has been formalized.

The JSON source of truth is `docs/phase2_completion_classification.json`; this Markdown is a readable rendering of the same entries.

## Class Definitions

- `textbook_proof_completed`: The task-facing statement is closed by local theorem/lemma-level source-route evidence rather than a private axiom or stronger Mathlib replacement.
- `mathlib_backed_adapter_completed`: The task-facing statement builds, but the main route specializes or adapts a stronger Mathlib theorem or Mathlib-facing bridge.
- `interface_bridge_completed`: The task proves a bridge between ToyApollo textbook objects and another interface; it is not itself a source proof completion claim.
- `open_math_debt`: The task still depends on a private axiom, public proof package, beyond-book package, or another explicit unproved mathematical obligation.
- `beyond_book_exception`: The task is intentionally outside the book proof scope; only thm_14_8_ProofBeyondBook may use this primary class.
- `needs_decision`: The task has audit or setup signals that require a separate proof-route review before being counted as textbook completed.

## Summary

| primary_class | count |
| --- | ---: |
| `textbook_proof_completed` | 14 |
| `mathlib_backed_adapter_completed` | 3 |
| `interface_bridge_completed` | 0 |
| `open_math_debt` | 13 |
| `beyond_book_exception` | 1 |
| `needs_decision` | 3 |

## Step 2.5 Tier A Outcomes

| task | outcome | targeted debt | note |
| --- | --- | --- | --- |
| `prob_10_5` | `needs_decision` | `prob_10_5_dominated_probability_to_mean_internal` | Current statement lacks theorem-level measurability and uniform-integrability bridge hypotheses for the available DCT/Vitali route. |
| `prob_10_6` | `textbook_proof_completed` | `prob_10_6_singleton_masses_to_distribution_internal` | Step 6B removed the private axiom and landed theorem-level arbitrary countable-space singleton-mass to bounded-test evidence. |
| `prob_11_6` | `needs_decision` | `prob_11_6_sixthMomentSupport_internal` | Sixth-moment expansion needs a reusable independent-sum moment layer plus explicit measurability, integrability, a.e. bound, and mixed-term cancellation landings. |
| `prob_11_9` | `needs_decision` | `prob_11_9_occupancy_moment_calculation_internal` | Current statement has no finite independent uniform balls-in-boxes model linking `X` to empty-box and two-box empty probabilities; `ex_6_5_2` is adjacent but only covers a different one-box exact-occupancy expectation. |

## Task Classifications

| task | primary class | flags | evidence | next action |
| --- | --- | --- | --- | --- |
| `ex_10_3_2` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/ex_10_3_2.lean:216` structure | Step 4 reviewed the public setup structures as source density/law data, not proof packages; no Step 4 repair remains. |
| `prob_10_5` | `needs_decision` | `public_interface_clean`, `private_axiom_internalized`, `ledger_unchanged` | `ToyApollo/Output/prob_10_5.lean:22` private_axiom | Decide whether to strengthen the public theorem with explicit measurability/uniform-integrability/Vitali hypotheses, add local bridge theorems, or keep this as open internal debt. |
| `prob_10_6` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_10_6.lean:287` theorem | Step 6B removed the private axiom and proved the arbitrary countable-space singleton-mass to bounded-test direction through PMF atomization, Tannery/dominated tsum convergence, and `PMF.integral_eq_tsum`. |
| `thm_10_8` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/thm_10_8.lean:91` structure | Step 4 reviewed `mkSkorokhodQuantileSupport` as theorem-level evidence consumed internally by the public theorem. |
| `prob_11_10` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `support_constructor_return_only`, `ledger_unchanged` | `ToyApollo/Output/prob_11_10.lean:64` private_axiom | Replace the private axiom with theorem-level finite-grid/continuous-CDF uniformization evidence. |
| `prob_11_5` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_11_5.lean:42` def | Step 4 reviewed tailSummabilitySupport as theorem-level p-series/Chebyshev evidence consumed internally by the public theorem. |
| `prob_11_6` | `needs_decision` | `public_interface_clean`, `private_axiom_internalized`, `support_constructor_return_only`, `ledger_unchanged` | `ToyApollo/Output/prob_11_6.lean:62` private_axiom | Decide whether to strengthen the random-variable interface with `AEStronglyMeasurable`/`MemLp` or a.e. bound landings, build a reusable independent finite-sum sixth-moment layer, or keep the sixth-moment expansion as internal debt. |
| `prob_11_7` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_11_7.lean:54` def | Step 4 reviewed the covariance-decay support route as theorem-level evidence consumed internally by the public theorem. |
| `prob_11_8` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `ledger_unchanged` | `ToyApollo/Output/prob_11_8.lean:41` private_axiom | Replace the private axiom with theorem-level covariance-decay evidence. |
| `prob_11_9` | `needs_decision` | `public_interface_clean`, `private_axiom_internalized`, `support_constructor_return_only`, `ledger_unchanged` | `ToyApollo/Output/prob_11_9.lean:55` private_axiom | Decide whether to rewrite or strengthen `prob_11_9` around an explicit occupancy model, possibly reusing `ex_6_5_2` ingredients but adding empty-box count and two-box joint probability lemmas, or keep this as internal debt. |
| `thm_11_7` | `open_math_debt` | `public_interface_leak`, `source_route_open`, `ledger_unchanged` | `ToyApollo/Output/thm_11_7.lean:257` theorem | Private axiom removed; final Borel-Cantelli/Theorem 10.1 assembly is theorem-level, but the fourth-moment expansion remains open as an explicit public tail-summability premise. |
| `ex_13_5_1` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/ex_13_5_1.lean:270` def | Step 4 reviewed rectangle/Fubini support as theorem-level evidence; no private axiom or public proof package remains. |
| `thm_13_12` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/thm_13_12.lean:418` theorem | Step 4 reviewed countablePartitionVersionSupport as theorem-level source-route evidence consumed internally. |
| `thm_13_13` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/thm_13_13.lean:177` def | Step 4 reviewed atomIntegralSupport as theorem-level joint-law evidence; no private axiom debt remains. |
| `thm_13_14` | `open_math_debt` | `public_interface_leak`, `source_route_open`, `ledger_unchanged` | `ToyApollo/Output/thm_13_14.lean:327` theorem | Private axiom removed; final conditional-expectation assembly is theorem-level, but interval Fubini and pi-lambda extension remain open as explicit public premises. |
| `ex_14_3_1` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/ex_14_3_1.lean:92` structure | Keep the source setup documented; no private proof debt is recorded for this law-level statement. |
| `ex_14_3_2` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/ex_14_3_2.lean:258` structure | Keep the source setup documented; no private proof debt is recorded for this law-level statement. |
| `ex_14_4_1` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `ledger_unchanged` | `ToyApollo/Output/ex_14_4_1.lean:76` private_axiom | Construct the thm_14_7_LindebergLevySetup route from Bernoulli source data at theorem level. |
| `ex_14_4_2` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `ledger_unchanged` | `ToyApollo/Output/ex_14_4_2.lean:126` private_axiom | Construct the thm_14_7_LindebergLevySetup route from Poisson source data at theorem level. |
| `ex_14_4_3` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `inherited_beyond_book_exception`, `ledger_unchanged` | `ToyApollo/Output/ex_14_4_3.lean:374` private_axiom | Replace the Lyapunov private axiom with theorem-level fourth-moment/Riemann-sum evidence while preserving inherited beyond-book classification. |
| `prob_14_1` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_1.lean:232` private_axiom | Prove finite urn mass and Stirling-to-Beta CDF convergence at theorem level, or keep both obligations explicitly open. |
| `prob_14_10` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_10.lean:103` private_axiom | Replace the private axiom with theorem-level bounded moments-to-MGF evidence. |
| `prob_14_11` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `inherited_beyond_book_exception`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_11.lean:60` private_axiom | Replace private axioms with theorem-level generalized coupon and Lyapunov evidence while preserving inherited beyond-book classification. |
| `prob_14_12` | `mathlib_backed_adapter_completed` | `public_interface_clean`, `interface_bridge_present`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_12.lean:247` theorem | Keep current setup public and documented; only upgrade the mean-convergence adapter if strict textbook-route formalization is later required. |
| `prob_14_2` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_2.lean:165` private_axiom | Construct the thm_14_7_LindebergLevySetup route from Gamma source data at theorem level. |
| `prob_14_3` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_14_3.lean:48` structure | Keep the setup public and documented as source data. |
| `prob_14_4` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_14_4.lean:38` structure | Keep the setup public and documented as source data. |
| `prob_14_7` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_14_7.lean:44` structure | Keep setup assumptions public and documented; no private proof-field debt is recorded for this statement. |
| `prob_14_8` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_8.lean:85` private_axiom | Replace the private axiom with theorem-level MGF-to-characteristic convergence evidence. |
| `prob_14_9` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_14_9.lean:35` structure | Keep setup public; consider audit allowlisting for reviewed source setup if review noise becomes costly. |
| `thm_14_5` | `mathlib_backed_adapter_completed` | `public_interface_clean`, `source_route_open`, `metadata_only_cleanliness_risk`, `mathlib_switch_without_textbook_route`, `interface_bridge_present`, `ledger_unchanged` | `ToyApollo/Output/thm_14_5.lean:430` theorem | Keep adapter classification unless the source-route lemmas are formalized and thm_14_5 is reassembled through thm_14_5_of_uniformTailBound. |
| `thm_14_6` | `mathlib_backed_adapter_completed` | `public_interface_clean`, `interface_bridge_present`, `mathlib_switch_without_textbook_route`, `ledger_unchanged` | `ToyApollo/Output/thm_14_6.lean:459` theorem | Keep Mathlib-backed adapter classification unless a textbook Prokhorov/Levy completion route is formalized locally. |
| `thm_14_7` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/thm_14_7.lean:205` structure | Formalize centering, independent-sum characteristic convergence, and normal characteristic identification at theorem level. |
| `thm_14_8` | `beyond_book_exception` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/thm_14_8.lean:167` structure | Preserve this boundary; downstream uses must be flagged as inherited_beyond_book_exception, not ordinary proved debt. |

## Audit Scope Notes

- Every task ID from `docs/phase2_ch10_14_clean_debt_surface_audit.json` is either represented as a task row here or folded into its parent task when the audit ID is an obligation-only row, such as `obl_thm_14_8_beyond_book_proof_obligations`.
- `public_setup_parameter_review` and `public_proof_package_return_review` are not treated as proof-completion evidence. They either become `needs_decision` rows or are combined with stronger task-specific evidence such as private axioms or Worker-D classification notes.
- `open_math_debt` remains visible when missing source proof is carried either by a private axiom or by an explicit statement-boundary premise. The latter is flagged as `public_interface_leak` / `source_route_open`, not hidden as completion.
- `mathlib_backed_adapter_completed` remains distinct from `textbook_proof_completed`; `thm_14_5`, `thm_14_6`, and `prob_14_12` are not counted as strict textbook proof completions.

## Validation

Commands to run for this classification pass:

- `python -m json.tool docs/phase2_completion_classification.json`
- `python tools/validate_phase2_completion_classification.py`
- `python -m unittest tests.test_phase2_completion_classification`
- `rg -n "project_ledger|open_math_debt|mathlib_backed_adapter_completed|thm_14_8_ProofBeyondBook" docs/phase2_completion_classification.md`
- `python tools/audit_phase2_clean_debt_surface.py --fail-on-errors`
- `lake env lean <each unique lean_file listed in docs/phase2_completion_classification.json>`

## Ledger Boundary

`project_ledger.json` was not edited by this classification pass. The classification is ledger-independent and records proof-route evidence separately from execution bookkeeping.

## Beyond-Book Boundary

`thm_14_8_ProofBeyondBook` is the only task with `primary_class = beyond_book_exception`. Downstream uses such as `ex_14_4_3` and `prob_14_11` are flagged as `inherited_beyond_book_exception`, not ordinary proved debt.
