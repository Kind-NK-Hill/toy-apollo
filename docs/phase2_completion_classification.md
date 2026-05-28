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
| `textbook_proof_completed` | 9 |
| `mathlib_backed_adapter_completed` | 3 |
| `interface_bridge_completed` | 0 |
| `open_math_debt` | 9 |
| `beyond_book_exception` | 1 |
| `needs_decision` | 12 |

## Step 2.5 Tier A Outcomes

| task | outcome | targeted debt | note |
| --- | --- | --- | --- |
| `prob_10_5` | `needs_decision` | `prob_10_5_dominated_probability_to_mean_internal` | Current statement lacks theorem-level measurability and uniform-integrability bridge hypotheses for the available DCT/Vitali route. |
| `prob_10_6` | `textbook_proof_completed` | `prob_10_6_singleton_masses_to_distribution_internal` | Step 6B removed the private axiom and landed theorem-level arbitrary countable-space singleton-mass to bounded-test evidence. |
| `prob_11_6` | `textbook_proof_completed` | `prob_11_6_sixthMomentSupport_internal` | Phase2 proof-production replaced the private sixth-moment axiom with theorem-level finite-sum expansion, singleton cancellation, uniform a.e. boundedness, and no-singleton tuple counting. |
| `prob_11_9` | `textbook_proof_completed` | `prob_11_9_occupancy_moment_calculation_internal` | Phase2 proof-production replaced the private occupancy second-moment axiom with theorem-level finite independent uniform balls-in-boxes evidence and source-facing quadratic mean convergence. |

## Task Classifications

| task | primary class | flags | evidence | next action |
| --- | --- | --- | --- | --- |
| `ex_10_3_2` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/ex_10_3_2.lean:216` structure<br>`ToyApollo/Output/ex_10_3_2.lean:327` structure<br>`ToyApollo/Output/ex_10_3_2.lean:360` theorem<br>+2 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `prob_10_5` | `needs_decision` | `public_interface_clean`, `private_axiom_internalized`, `ledger_unchanged` | `ToyApollo/Output/prob_10_5.lean:22` private_axiom<br>`ToyApollo/Output/prob_10_5.lean:32` theorem<br>`phase2_prompt_packs/prob_10_5/proof_obligations.json:3` metadata_note | Decide whether to strengthen the public theorem with explicit measurability/uniform-integrability/Vitali hypotheses, add local bridge theorems, or keep this as open internal debt. |
| `prob_10_6` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_10_6.lean:287` theorem<br>`ToyApollo/Output/prob_10_6.lean:323` theorem<br>`phase2_prompt_packs/prob_10_6/proof_obligations.json:3` metadata_note<br>+1 more | No Step 5.6 contract action remains for prob_10_6; keep the validator command in the classification evidence set. |
| `thm_10_8` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/thm_10_8.lean:91` structure<br>`ToyApollo/Output/thm_10_8.lean:101` theorem<br>`ToyApollo/Output/thm_10_8.lean:115` theorem<br>+2 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `prob_11_10` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_11_10.lean:377` theorem<br>`ToyApollo/Output/prob_11_10.lean:457` theorem<br>`ToyApollo/Output/prob_11_10.lean:493` theorem<br>+2 more | No prob_11_10 proof-production action remains; downstream tasks may consume the textbook completed theorem. |
| `prob_11_5` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/prob_11_5.lean:42` def<br>`ToyApollo/Output/prob_11_5.lean:126` theorem<br>`ToyApollo/Output/prob_11_5.lean:189` theorem<br>+2 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `prob_11_6` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_11_6.lean:54` theorem<br>`ToyApollo/Output/prob_11_6.lean:501` theorem<br>`ToyApollo/Output/prob_11_6.lean:666` theorem<br>+2 more | No prob_11_6 proof-production action remains; keep the Phase2 contract validators in the evidence loop. |
| `prob_11_7` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/prob_11_7.lean:54` def<br>`ToyApollo/Output/prob_11_7.lean:472` theorem<br>`ToyApollo/Output/prob_11_7.lean:538` theorem<br>+2 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `prob_11_8` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_11_8.lean:27` def<br>`ToyApollo/Output/prob_11_8.lean:74` theorem<br>`ToyApollo/Output/prob_11_8.lean:146` theorem<br>+2 more | No prob_11_8 proof-production action remains; keep the Phase2 contract validators in the evidence loop. |
| `prob_11_9` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/prob_11_9.lean:258` def<br>`ToyApollo/Output/prob_11_9.lean:271` theorem<br>`ToyApollo/Output/prob_11_9.lean:292` theorem<br>+4 more | No prob_11_9 proof-production action remains; keep the Phase2 contract validators in the evidence loop. |
| `thm_11_7` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/thm_11_7.lean:550` theorem<br>`ToyApollo/Output/thm_11_7.lean:364` theorem<br>`ToyApollo/Output/thm_11_7.lean:1118` theorem<br>`ToyApollo/Output/thm_11_7.lean:1087` theorem<br>`ToyApollo/Output/thm_11_7.lean:1137` theorem<br>`ToyApollo/Output/thm_11_7.lean:1160` theorem<br>`phase2_prompt_packs/thm_11_7/proof_obligations.json:155` proof_contract<br>`phase2_prompt_packs/thm_11_7/proof_obligations.json:159` proof_contract | Self-correction restored the public fourth-moment package to the uncentered textbook assumption and derives the centered package internally; no `thm_11_7` source-route proof action remains. |
| `ex_13_5_1` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/ex_13_5_1.lean:270` def<br>`ToyApollo/Output/ex_13_5_1.lean:400` def<br>`ToyApollo/Output/ex_13_5_1.lean:416` theorem<br>+2 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `thm_13_12` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/thm_13_12.lean:418` theorem<br>`ToyApollo/Output/thm_13_12.lean:505` theorem<br>`docs/phase2_ch10_14_clean_debt_surface_audit.md:108` audit_signal<br>+1 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `thm_13_13` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/thm_13_13.lean:177` def<br>`ToyApollo/Output/thm_13_13.lean:187` theorem<br>`ToyApollo/Output/thm_13_13.lean:239` theorem<br>+2 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `thm_13_14` | `textbook_proof_completed` | `public_interface_clean`, `interface_bridge_present`, `ledger_unchanged` | `ToyApollo/Output/thm_13_14.lean:818` theorem<br>`ToyApollo/Output/thm_13_14.lean:835` theorem<br>`ToyApollo/Output/thm_13_14.lean:538` theorem<br>`phase2_prompt_packs/thm_13_14/proof_obligations.json:174` proof_contract<br>+8 more | No `thm_13_14` proof-production action remains; public proof-package premises are absent, kernel measurability/integrability is internal, and the source Fubini plus pi-lambda route is theorem-level. |
| `ex_14_3_1` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/ex_14_3_1.lean:92` structure<br>`ToyApollo/Output/ex_14_3_1.lean:74` theorem<br>`ToyApollo/Output/ex_14_3_1.lean:127` theorem<br>+3 more | Keep as Level 0 direct statement/setup unless a later source-route review introduces concrete proof obligations. |
| `ex_14_3_2` | `textbook_proof_completed` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/ex_14_3_2.lean:258` structure<br>`ToyApollo/Output/ex_14_3_2.lean:220` theorem<br>`ToyApollo/Output/ex_14_3_2.lean:294` theorem<br>+3 more | Keep as Level 0 direct statement/setup unless a later source-route review introduces concrete proof obligations. |
| `ex_14_4_1` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `ledger_unchanged` | `ToyApollo/Output/ex_14_4_1.lean:76` private_axiom<br>`ToyApollo/Output/ex_14_4_1.lean:96` theorem<br>`docs/phase2_ch10_14_clean_debt_surface_audit.md:38` audit_signal<br>+1 more | Construct the thm_14_7_LindebergLevySetup route from Bernoulli source data at theorem level. |
| `ex_14_4_2` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `ledger_unchanged` | `ToyApollo/Output/ex_14_4_2.lean:126` private_axiom<br>`ToyApollo/Output/ex_14_4_2.lean:158` theorem<br>`docs/phase2_ch10_14_clean_debt_surface_audit.md:41` audit_signal<br>+1 more | Construct the thm_14_7_LindebergLevySetup route from Poisson source data at theorem level. |
| `ex_14_4_3` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `inherited_beyond_book_exception`, `ledger_unchanged` | `ToyApollo/Output/ex_14_4_3.lean:374` private_axiom<br>`ToyApollo/Output/ex_14_4_3.lean:380` theorem<br>`ToyApollo/Output/ex_14_4_3.lean:382` public_parameter<br>+3 more | Replace the Lyapunov private axiom with theorem-level fourth-moment/Riemann-sum evidence while preserving inherited beyond-book classification. |
| `prob_14_1` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_1.lean:232` private_axiom<br>`ToyApollo/Output/prob_14_1.lean:212` structure<br>`ToyApollo/Output/prob_14_1.lean:307` theorem<br>+2 more | Prove finite urn mass and Stirling-to-Beta CDF convergence at theorem level, or keep both obligations explicitly open. |
| `prob_14_10` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_10.lean:103` private_axiom<br>`ToyApollo/Output/prob_14_10.lean:86` structure<br>`ToyApollo/Output/prob_14_10.lean:158` theorem<br>+2 more | Replace the private axiom with theorem-level bounded moments-to-MGF evidence. |
| `prob_14_11` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `inherited_beyond_book_exception`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_11.lean:60` private_axiom<br>`ToyApollo/Output/prob_14_11.lean:66` private_axiom<br>`ToyApollo/Output/prob_14_11.lean:75` private_axiom<br>+5 more | Replace private axioms with theorem-level generalized coupon and Lyapunov evidence while preserving inherited beyond-book classification. |
| `prob_14_12` | `mathlib_backed_adapter_completed` | `public_interface_clean`, `interface_bridge_present`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_12.lean:247` theorem<br>`ToyApollo/Output/prob_14_12.lean:302` interface_bridge<br>`ToyApollo/Output/prob_14_12.lean:364` theorem<br>+3 more | Keep current setup public and documented; only upgrade the mean-convergence adapter if strict textbook-route formalization is later required. |
| `prob_14_2` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_2.lean:165` private_axiom<br>`ToyApollo/Output/prob_14_2.lean:145` structure<br>`ToyApollo/Output/prob_14_2.lean:185` theorem<br>+2 more | Construct the thm_14_7_LindebergLevySetup route from Gamma source data at theorem level. |
| `prob_14_3` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/prob_14_3.lean:48` structure<br>`ToyApollo/Output/prob_14_3.lean:64` theorem<br>`ToyApollo/Output/prob_14_3.lean:201` theorem<br>+3 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `prob_14_4` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/prob_14_4.lean:38` structure<br>`ToyApollo/Output/prob_14_4.lean:64` theorem<br>`ToyApollo/Output/prob_14_4.lean:105` theorem<br>+3 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `prob_14_7` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/prob_14_7.lean:44` structure<br>`ToyApollo/Output/prob_14_7.lean:100` theorem<br>`ToyApollo/Output/prob_14_7.lean:133` theorem<br>+3 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `prob_14_8` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/prob_14_8.lean:85` private_axiom<br>`ToyApollo/Output/prob_14_8.lean:64` structure<br>`ToyApollo/Output/prob_14_8.lean:129` theorem<br>+2 more | Replace the private axiom with theorem-level MGF-to-characteristic convergence evidence. |
| `prob_14_9` | `needs_decision` | `public_interface_clean`, `ledger_unchanged`, `metadata_only_cleanliness_risk` | `ToyApollo/Output/prob_14_9.lean:35` structure<br>`ToyApollo/Output/prob_14_9.lean:140` theorem<br>`ToyApollo/Output/prob_14_9.lean:165` theorem<br>+3 more | Run Step 6A source-route extraction/signature freeze for this task, then either add honest verified proof_contract evidence or keep/reclassify the task as adapter, bridge, or open debt. |
| `thm_14_5` | `mathlib_backed_adapter_completed` | `public_interface_clean`, `source_route_open`, `metadata_only_cleanliness_risk`, `mathlib_switch_without_textbook_route`, `interface_bridge_present`, `ledger_unchanged` | `ToyApollo/Output/thm_14_5.lean:430` theorem<br>`ToyApollo/Output/thm_14_5.lean:437` mathlib_adapter<br>`ToyApollo/Output/thm_14_5.lean:442` interface_bridge<br>+1 more | Keep adapter classification unless the source-route lemmas are formalized and thm_14_5 is reassembled through thm_14_5_of_uniformTailBound. |
| `thm_14_6` | `mathlib_backed_adapter_completed` | `public_interface_clean`, `interface_bridge_present`, `mathlib_switch_without_textbook_route`, `ledger_unchanged` | `ToyApollo/Output/thm_14_6.lean:459` theorem<br>`ToyApollo/Output/thm_14_6.lean:464` mathlib_adapter<br>`ToyApollo/Output/thm_14_6.lean:491` interface_bridge<br>+2 more | Keep Mathlib-backed adapter classification unless a textbook Prokhorov/Levy completion route is formalized locally. |
| `thm_14_7` | `open_math_debt` | `public_interface_clean`, `private_axiom_internalized`, `setup_parameter_review_needed`, `ledger_unchanged` | `ToyApollo/Output/thm_14_7.lean:205` structure<br>`ToyApollo/Output/thm_14_7.lean:226` private_axiom<br>`ToyApollo/Output/thm_14_7.lean:261` theorem<br>+2 more | Formalize centering, independent-sum characteristic convergence, and normal characteristic identification at theorem level. |
| `thm_14_8` | `beyond_book_exception` | `public_interface_clean`, `ledger_unchanged` | `ToyApollo/Output/thm_14_8.lean:167` structure<br>`ToyApollo/Output/thm_14_8.lean:195` theorem<br>`docs/phase2_ch10_14_clean_debt_surface_audit.md:116` audit_signal<br>+1 more | Preserve this boundary; downstream uses must be flagged as inherited_beyond_book_exception, not ordinary proved debt. |

## Step 5.6 Contract Reconciliation Note

The strict proof-contract gate is now reflected in the JSON source of truth. Rows that only had build/public-surface evidence from the Good Corpus pass, but no verified `proof_contract` evidence, are downgraded to `needs_decision` pending Step 6A route extraction and signature freeze. `prob_10_6` remains `textbook_proof_completed` because its task-local proof-obligation contracts were checked and the task audit is clean. `ex_14_3_1` and `ex_14_3_2` remain `textbook_proof_completed` as Level 0 direct statement/setup rows with no task-local proof obligations in scope.
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
