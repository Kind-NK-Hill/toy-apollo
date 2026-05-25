# Phase2 Step 4 Good Corpus Family Work Queue

Created: 2026-05-24
Status: Step 4 queue completed on dirty local baseline

This queue is the execution companion to `docs/modification_0525_steps/phase2_step4_good_corpus_lean_repair_implementation_plan.md`.

Step 4 is complete only when every row below has a final Step 4 outcome:

- `good_corpus_closed`
- `good_corpus_adapter_marked`
- `good_corpus_open_debt_exposed`
- `good_corpus_needs_decision`
- `good_corpus_beyond_book_exception`
- `good_corpus_exception_inherited`

Do not use ledger state as the completion signal.

## Current Global Baseline

Inputs:

- `docs/phase2_completion_classification.md`
- `docs/phase2_completion_classification.json`
- `docs/modification_0525_steps/phase2_interface_bridge_inventory.md`
- `docs/modification_0525_steps/phase2_step2_5_step1_unfinished_wrapup_plan.md`

Known baseline facts:

- Step 2 classification exists.
- Step 2.5 Tier A tasks were processed and marked `needs_decision`.
- Step 3 inventory exists and identifies family-level bridge/reuse gaps.
- The repository may be dirty from Step 1/2/2.5/3 work; checkpoint before Step 4 implementation if the user authorizes it.

Queue completeness guard:

- Every task in `docs/phase2_completion_classification.json` with `open_math_debt`, `needs_decision`, `mathlib_backed_adapter_completed`, or `beyond_book_exception` must appear in one of the family tables below.
- A task with review-only audit status still belongs in this queue if classification says its support-return constructor, setup parameter, adapter status, or open debt needs a Step 4 outcome.
- Some rows are non-classification review items. Mark these explicitly as `concept_bridge_review` or `read_only_adapter_check`; they do not need a `primary_class` mapping unless they become task-level completion claims.
- Do not call Step 4 complete until the family table and classification file agree on coverage.

Execution columns:

- Fill `final outcome` only after the row has been reviewed or repaired.
- Fill `evidence/landing` with theorem/lemma names, private axiom names, adapter declarations, or bridge inventory lines.
- Fill `validation run` with the actual Lean/audit/classification command result used to close the row.
- Leave these cells as `pending` before execution; do not delete the columns.

## Family 4.2: Ch10 Convergence / Distribution

| priority | task | target files | current known issue | Step 4 action | expected outcome | final outcome | evidence/landing | validation run |
| ---: | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `prob_10_6` | `ToyApollo/Output/prob_10_6.lean`; `phase2_prompt_packs/prob_10_6/proof_obligations.json` | Reverse singleton-mass-to-bounded-test direction is private axiom; `prob_14_5` and `tv_distance_core` provide related but not directly wired theorem material. | Decide whether to generalize a countable-space TV bridge or keep as `needs_decision`; do not reintroduce `h_countable_bridge`. | `good_corpus_needs_decision` or `good_corpus_closed` | `good_corpus_needs_decision` | `ToyApollo/Output/prob_10_6.lean:58` private axiom; final theorem `ToyApollo/Output/prob_10_6.lean:66`; no public countability bridge parameter found. | `lake env lean ToyApollo/Output/prob_10_6.lean` passed; public signature scan passed; global audit passed. |
| 2 | `prob_10_5` | `ToyApollo/Output/prob_10_5.lean`; `phase2_prompt_packs/prob_10_5/proof_obligations.json` | Convergence in probability plus domination to mean convergence is private axiom; Ch7 DCT does not match the interface. | Decide between Vitali/subsequence-DCT bridge and statement rewrite; keep adapter/open debt honest. | `good_corpus_needs_decision` or `good_corpus_closed` | `good_corpus_needs_decision` | `ToyApollo/Output/prob_10_5.lean:22` private axiom; final theorem `ToyApollo/Output/prob_10_5.lean:32`; no public DCT bridge parameter found. | `lake env lean ToyApollo/Output/prob_10_5.lean` passed; public signature scan passed; global audit passed. |
| 3 | `prob_10_10_distribution_bridge` | `ToyApollo/Output/prob_10_10_distribution_bridge.lean` | `concept_bridge_review`: bridge file is not a normal classification task row, but later distribution tasks may depend on its interface claim. | Inspect theorem bodies; update `docs/modification_0525_steps/phase2_interface_bridge_inventory.md` if the bridge is actual theorem evidence or hidden debt. | bridge review recorded; no `primary_class` mapping unless promoted to task classification | `good_corpus_adapter_marked` | Bridge review recorded: `ToyApollo/Output/prob_10_10_distribution_bridge.lean:21` and `:33` are theorem declarations, not private axioms. | `lake env lean ToyApollo/Output/prob_10_10_distribution_bridge.lean` passed; no inventory change needed. |
| 4 | `prob_14_5` | `ToyApollo/Output/prob_14_5.lean`; `phase2_prompt_packs/prob_14_5/proof_obligations.json` | `concept_bridge_review`: integer-valued TV/weak equivalence is a concrete reuse seed for `prob_10_6`, but it is specialized to `ℤ`. | Inspect theorem landings from `prob_14_5` and decide whether they can support a general countable-space bridge or only serve as a model. | bridge review recorded; no `primary_class` mapping unless promoted to task classification | `good_corpus_adapter_marked` | Bridge seed recorded: `ToyApollo/Output/prob_14_5.lean:100`, `:180`, `:254`, and `:296`; specialized to integer-valued laws, so it does not close `prob_10_6`. | `lake env lean ToyApollo/Output/prob_14_5.lean` passed; no inventory change needed. |
| 5 | `thm_10_8` | `ToyApollo/Output/thm_10_8.lean`; `phase2_prompt_packs/thm_10_8/proof_obligations.json` | Quantile support constructor should remain internal/theorem-level, not public leak. | Verify public theorem surface and support constructor landing; update classification if needed. | `good_corpus_closed` or `good_corpus_needs_decision` | `good_corpus_closed` | `mkSkorokhodQuantileSupport` at `ToyApollo/Output/thm_10_8.lean:101` constructs support internally; public theorem at `:115` has no support parameter. | `lake env lean ToyApollo/Output/thm_10_8.lean` passed; public signature scan passed. |
| 6 | `ex_10_3_2` | `ToyApollo/Output/ex_10_3_2.lean`; `phase2_prompt_packs/ex_10_3_2/proof_obligations.json` | Two setup structures are public; classification marks setup-parameter review needed. | Decide whether the setup structures are source data or hide proof obligations; record any statement-decision requirement. | `good_corpus_needs_decision` or `good_corpus_closed` | `good_corpus_closed` | Setup structures at `ToyApollo/Output/ex_10_3_2.lean:216` and `:327` are source density/law data; theorem landings at `:233` and `:340` build without private axiom. | `lake env lean ToyApollo/Output/ex_10_3_2.lean` passed; public signature scan recorded source-data setup only. |

Validation:

```powershell
lake env lean ToyApollo/Output/prob_10_5.lean
lake env lean ToyApollo/Output/prob_10_6.lean
lake env lean ToyApollo/Output/prob_10_10_distribution_bridge.lean
lake env lean ToyApollo/Output/prob_14_5.lean
lake env lean ToyApollo/Output/thm_10_8.lean
lake env lean ToyApollo/Output/ex_10_3_2.lean
```

## Family 4.3: Ch11 Estimate

| priority | task | target files | current known issue | Step 4 action | expected outcome | final outcome | evidence/landing | validation run |
| ---: | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `prob_11_6` | `ToyApollo/Output/prob_11_6.lean`; `phase2_prompt_packs/prob_11_6/proof_obligations.json` | Sixth-moment support is private axiom; downstream tail route is theorem-level after support. | Keep `needs_decision` unless a moment-expansion theorem is added; ensure no fake proved metadata. | `good_corpus_needs_decision` | `good_corpus_needs_decision` | `ToyApollo/Output/prob_11_6.lean:62` private axiom; final theorem `:205`; no public support parameter found. | `lake env lean ToyApollo/Output/prob_11_6.lean` passed; global audit passed. |
| 2 | `prob_11_9` | `ToyApollo/Output/prob_11_9.lean`; `phase2_prompt_packs/prob_11_9/proof_obligations.json` | Occupancy moment calculation is private axiom; Ch6 occupancy model is adjacent but not matching. | Decide whether to rewrite around explicit finite occupancy model or keep open. | `good_corpus_needs_decision` | `good_corpus_needs_decision` | `ToyApollo/Output/prob_11_9.lean:55` private axiom; final theorem `:150`; Ch6 occupancy remains adjacent only. | `lake env lean ToyApollo/Output/prob_11_9.lean` passed; global audit passed. |
| 3 | `prob_11_5` | `ToyApollo/Output/prob_11_5.lean`; `phase2_prompt_packs/prob_11_5/proof_obligations.json` | Tail-summability support constructor returns support; classification marks support-return review needed. | Verify the constructor is theorem-level evidence and that metadata does not land on support fields. | `good_corpus_closed` or `good_corpus_needs_decision` | `good_corpus_closed` | `prob_11_5_tailSummability_of_variance_growth` at `ToyApollo/Output/prob_11_5.lean:126`; final theorem at `:189` constructs support internally. | `lake env lean ToyApollo/Output/prob_11_5.lean` passed; support-return review passed. |
| 4 | `prob_11_7` | `ToyApollo/Output/prob_11_7.lean`; `phase2_prompt_packs/prob_11_7/proof_obligations.json` | Covariance-decay support constructor returns support; classification marks support-return review needed. | Review covariance-decay proof route and decide whether the support return is evidence or hidden proof package. | `good_corpus_closed` or `good_corpus_needs_decision` | `good_corpus_closed` | `prob_11_7_sampleMeanVarianceSupport_of_covarianceDecay` at `ToyApollo/Output/prob_11_7.lean:472`; final theorem at `:538` uses it internally. | `lake env lean ToyApollo/Output/prob_11_7.lean` passed; support-return review passed. |
| 5 | `prob_11_8` | `ToyApollo/Output/prob_11_8.lean`; `phase2_prompt_packs/prob_11_8/proof_obligations.json` | AR(1) covariance decay remains private axiom. | Expose missing MemLp/variance/covariance-recursion prerequisites; keep debt explicit. | `good_corpus_open_debt_exposed` or `good_corpus_needs_decision` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/prob_11_8.lean:41` private axiom; final theorem `:49`; open covariance-decay debt remains explicit. | `lake env lean ToyApollo/Output/prob_11_8.lean` passed; global audit passed. |
| 6 | `prob_11_10` | `ToyApollo/Output/prob_11_10.lean`; `phase2_prompt_packs/prob_11_10/proof_obligations.json` | Continuous-grid uniformization remains private axiom. | Keep as open debt unless theorem-level uniformization prerequisites are added. | `good_corpus_open_debt_exposed` or `good_corpus_needs_decision` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/prob_11_10.lean:64` private axiom; final theorem `:71`; uniformization debt remains explicit. | `lake env lean ToyApollo/Output/prob_11_10.lean` passed; global audit passed. |
| 7 | `thm_11_7` | `ToyApollo/Output/thm_11_7.lean`; `phase2_prompt_packs/thm_11_7/proof_obligations.json` | Fourth-moment tail summability remains private axiom. | Ensure final theorem does not expose proof package; classify estimate gap honestly. | `good_corpus_open_debt_exposed` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/thm_11_7.lean:244` private axiom; final theorem `:262`; no public proof package parameter found. | `lake env lean ToyApollo/Output/thm_11_7.lean` passed; global audit passed. |

Validation:

```powershell
lake env lean ToyApollo/Output/prob_11_5.lean
lake env lean ToyApollo/Output/prob_11_6.lean
lake env lean ToyApollo/Output/prob_11_7.lean
lake env lean ToyApollo/Output/prob_11_8.lean
lake env lean ToyApollo/Output/prob_11_9.lean
lake env lean ToyApollo/Output/prob_11_10.lean
lake env lean ToyApollo/Output/thm_11_7.lean
```

## Family 4.4: Ch13 Measure / Fubini

| priority | task | target files | current known issue | Step 4 action | expected outcome | final outcome | evidence/landing | validation run |
| ---: | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `thm_13_14` | `ToyApollo/Output/thm_13_14.lean`; `phase2_prompt_packs/thm_13_14/proof_obligations.json` | Fubini/pi-lambda route still private axiom. | Keep public interface clean; classify density/Fubini/extension route as open unless theorem-level lemmas are added. | `good_corpus_open_debt_exposed` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/thm_13_14.lean:327` private axiom; open density/Fubini extension route remains explicit. | `lake env lean ToyApollo/Output/thm_13_14.lean` passed; global audit passed. |
| 2 | `thm_13_12` | `ToyApollo/Output/thm_13_12.lean`; `phase2_prompt_packs/thm_13_12/proof_obligations.json` | Countable partition support returns need review. | Confirm support constructor is theorem-level evidence, not public proof package. | `good_corpus_closed` or `good_corpus_needs_decision` | `good_corpus_closed` | `thm_13_12_countablePartitionVersionSupport` at `ToyApollo/Output/thm_13_12.lean:418`; final theorem at `:505` uses theorem-level support internally. | `lake env lean ToyApollo/Output/thm_13_12.lean` passed; support-return review passed. |
| 3 | `thm_13_13` | `ToyApollo/Output/thm_13_13.lean`; `phase2_prompt_packs/thm_13_13/proof_obligations.json` | Atom-integral support needs proof-route classification. | Confirm atom integral proof is theorem-level or mark adapter/open debt. | `good_corpus_closed` or `good_corpus_adapter_marked` | `good_corpus_closed` | `thm_13_13_atomIntegral_from_jointLaw` at `ToyApollo/Output/thm_13_13.lean:187`; final theorem at `:239`; no private axiom found. | `lake env lean ToyApollo/Output/thm_13_13.lean` passed; support-return review passed. |
| 4 | `ex_13_5_1` | `ToyApollo/Output/ex_13_5_1.lean`; `phase2_prompt_packs/ex_13_5_1/proof_obligations.json` | Rectangle/Fubini/pi-lambda support constructors need review. | Confirm support constructors are theorem-level evidence and not fake proved fields. | `good_corpus_closed` or `good_corpus_needs_decision` | `good_corpus_closed` | `ex_13_5_1_rectangleAreaSupport_of_uniformSquareLaw` at `ToyApollo/Output/ex_13_5_1.lean:278`; final theorem at `:416`; no private axiom found. | `lake env lean ToyApollo/Output/ex_13_5_1.lean` passed; support-return review passed. |

Validation:

```powershell
lake env lean ToyApollo/Output/thm_13_14.lean
lake env lean ToyApollo/Output/thm_13_12.lean
lake env lean ToyApollo/Output/thm_13_13.lean
lake env lean ToyApollo/Output/ex_13_5_1.lean
```

## Family 4.5: Ch14 CLT / Tightness

| priority | task | target files | current known issue | Step 4 action | expected outcome | final outcome | evidence/landing | validation run |
| ---: | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | `thm_14_1` | `ToyApollo/Output/thm_14_1.lean` | `read_only_adapter_check`: not a current classification row, but it anchors the characteristic-function/weak-convergence adapter surface used by the Ch14 family. | Inspect public interface and proof route; update bridge inventory/family notes if adapter status changes. | read-only adapter check recorded; no `primary_class` mapping unless promoted to task classification | `good_corpus_adapter_marked` | Read-only adapter check recorded: `ToyApollo/Output/thm_14_1.lean:127`, `:176`, and `:202`; Mathlib characteristic/tightness route remains explicit. | `lake env lean ToyApollo/Output/thm_14_1.lean` passed; no inventory change needed. |
| 2 | `thm_14_2` | `ToyApollo/Output/thm_14_2.lean` | `read_only_adapter_check`: not a current classification row, but it anchors distribution-to-weak bridge material used by Ch14 and Ch10 bridge reasoning. | Inspect public interface and proof route; update bridge inventory/family notes if adapter status changes. | read-only adapter check recorded; no `primary_class` mapping unless promoted to task classification | `good_corpus_adapter_marked` | Read-only bridge check recorded: `ToyApollo/Output/thm_14_2.lean:224` and `:324`; distribution-to-weak bridge remains theorem-level. | `lake env lean ToyApollo/Output/thm_14_2.lean` passed; no inventory change needed. |
| 3 | `thm_14_5` | `ToyApollo/Output/thm_14_5.lean`; `phase2_prompt_packs/thm_14_5/proof_obligations.json` | Public theorem is Mathlib-backed tightness adapter; source spine remains open. | Keep adapter classification and source-route debt honest. | `good_corpus_adapter_marked` | `good_corpus_adapter_marked` | `ToyApollo/Output/thm_14_5.lean:430` final theorem; Mathlib adapter call at `:437`; local bridge at `:442`; source spine at `:371` not treated as textbook completion. | `lake env lean ToyApollo/Output/thm_14_5.lean` passed; adapter classification retained. |
| 4 | `thm_14_6` | `ToyApollo/Output/thm_14_6.lean`; `phase2_prompt_packs/thm_14_6/proof_obligations.json` | Main theorem is Mathlib-backed/bridge route; `hbridge` should not leak. | Confirm no public `hbridge`; classify adapter/bridge status. | `good_corpus_adapter_marked` | `good_corpus_adapter_marked` | `ToyApollo/Output/thm_14_6.lean:459` final theorem; Mathlib compactness route at `:464`; `thm_14_6_of_interval_tight` at `:487` has no public `hbridge`. | `lake env lean ToyApollo/Output/thm_14_6.lean` passed; public signature scan found no `hbridge`. |
| 5 | `prob_14_6` | `ToyApollo/Output/prob_14_6.lean`; `phase2_prompt_packs/prob_14_6/proof_obligations.json` | `read_only_adapter_check`: `prob_14_6_PositiveScalingSupport` remains internal and currently has no public leak, but Step 4 should explicitly record the support-surface review. | Verify support constructor/public theorem surface; record that no Lean repair is needed unless hidden proof debt is found. | read-only support/adapter check recorded; no `primary_class` mapping unless promoted to task classification | `good_corpus_closed` | Read-only support review recorded: `ToyApollo/Output/prob_14_6.lean:40` support surface; private helper theorems only; final theorem at `:221` has no support parameter. | `lake env lean ToyApollo/Output/prob_14_6.lean` passed; public signature scan passed. |
| 6 | `prob_14_12` | `ToyApollo/Output/prob_14_12.lean`; `phase2_prompt_packs/prob_14_12/proof_obligations.json` | Mean route is Mathlib-backed/interface evidence rather than strict textbook route. | Keep adapter classification explicit; do not promote to textbook proof completion without source-route rework. | `good_corpus_adapter_marked` | `good_corpus_adapter_marked` | `ToyApollo/Output/prob_14_12.lean:247`, `:302`, `:364`, and `:375`; setup is source data and route remains adapter-backed. | `lake env lean ToyApollo/Output/prob_14_12.lean` passed; adapter classification retained. |
| 7 | `thm_14_7` | `ToyApollo/Output/thm_14_7.lean`; `phase2_prompt_packs/thm_14_7/proof_obligations.json` | Lindeberg-Levy setup still contains private/open characteristic-expansion debt. | Keep open debt explicit; do not mark CLT setup as textbook completed. | `good_corpus_open_debt_exposed` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/thm_14_7.lean:226` private axiom; final theorem at `:261`; characteristic-expansion debt remains explicit. | `lake env lean ToyApollo/Output/thm_14_7.lean` passed; global audit passed. |
| 8 | `thm_14_8` | `ToyApollo/Output/thm_14_8.lean`; `phase2_prompt_packs/thm_14_8/proof_obligations.json` | Root `thm_14_8_ProofBeyondBook` is the only allowed beyond-book exception. | Preserve the root exception boundary; ensure it is not copied into other tasks as ordinary proof debt. | `good_corpus_beyond_book_exception` | `good_corpus_beyond_book_exception` | Root exception boundary at `ToyApollo/Output/thm_14_8.lean:167`; theorem landings at `:175`, `:184`, and `:195`. | `lake env lean ToyApollo/Output/thm_14_8.lean` passed; classification validator enforces this as sole beyond-book primary class. |
| 9 | `prob_14_2` | `ToyApollo/Output/prob_14_2.lean`; `phase2_prompt_packs/prob_14_2/proof_obligations.json` | Gamma source-to-Lindeberg-Levy setup is private/open debt. | Expose setup debt and decide whether to build theorem-level Gamma characteristic route. | `good_corpus_open_debt_exposed` or `good_corpus_needs_decision` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/prob_14_2.lean:165` private axiom; final theorem at `:185`; setup debt remains explicit. | `lake env lean ToyApollo/Output/prob_14_2.lean` passed; global audit passed. |
| 10 | `ex_14_4_1` | `ToyApollo/Output/ex_14_4_1.lean`; `phase2_prompt_packs/ex_14_4_1/proof_obligations.json` | Bernoulli source-to-Lindeberg-Levy setup is private/open debt. | Expose setup debt and avoid marking Bernoulli CLT setup as textbook completed. | `good_corpus_open_debt_exposed` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/ex_14_4_1.lean:76` private axiom; final theorem at `:96`; Bernoulli setup debt remains explicit. | `lake env lean ToyApollo/Output/ex_14_4_1.lean` passed; global audit passed. |
| 11 | `ex_14_4_2` | `ToyApollo/Output/ex_14_4_2.lean`; `phase2_prompt_packs/ex_14_4_2/proof_obligations.json` | Poisson source-to-Lindeberg-Levy setup is private/open debt. | Expose setup debt and avoid marking Poisson CLT setup as textbook completed. | `good_corpus_open_debt_exposed` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/ex_14_4_2.lean:126` private axiom; final theorem at `:158`; Poisson setup debt remains explicit. | `lake env lean ToyApollo/Output/ex_14_4_2.lean` passed; global audit passed. |
| 12 | `ex_14_4_3` | `ToyApollo/Output/ex_14_4_3.lean`; `phase2_prompt_packs/ex_14_4_3/proof_obligations.json` | Lyapunov verification remains private axiom; inherited beyond-book exception remains. | Keep `thm_14_8_ProofBeyondBook` inherited only; expose Lyapunov debt. | `good_corpus_exception_inherited` plus `good_corpus_open_debt_exposed` | `good_corpus_exception_inherited` plus `good_corpus_open_debt_exposed` | `ToyApollo/Output/ex_14_4_3.lean:374` private axiom; inherited `thm_14_8_ProofBeyondBook` use at `:382` and `:396`; final theorem at `:394`. | `lake env lean ToyApollo/Output/ex_14_4_3.lean` passed; inherited exception kept separate. |
| 13 | `prob_14_1` | `ToyApollo/Output/prob_14_1.lean`; `phase2_prompt_packs/prob_14_1/proof_obligations.json` | Polya/Stirling setup debt remains. | Keep public setup source data separate from proof fields; expose private debt. | `good_corpus_open_debt_exposed` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/prob_14_1.lean:232` private axiom; theorem landings at `:291`, `:298`, and `:307`; Stirling/CDF debt remains explicit. | `lake env lean ToyApollo/Output/prob_14_1.lean` passed; global audit passed. |
| 14 | `prob_14_8` | `ToyApollo/Output/prob_14_8.lean`; `phase2_prompt_packs/prob_14_8/proof_obligations.json` | MGF-to-characteristic convergence remains private/open debt. | Classify bridge/proof gap honestly. | `good_corpus_open_debt_exposed` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/prob_14_8.lean:85` private axiom; theorem landings at `:93`, `:102`, `:117`, and `:129`; MGF-to-characteristic gap remains explicit. | `lake env lean ToyApollo/Output/prob_14_8.lean` passed; global audit passed. |
| 15 | `prob_14_10` | `ToyApollo/Output/prob_14_10.lean`; `phase2_prompt_packs/prob_14_10/proof_obligations.json` | Moments-to-MGF setup debt remains. | Expose bounded moment/MGF gap, preserve proved weak-to-moment route. | `good_corpus_open_debt_exposed` | `good_corpus_open_debt_exposed` | `ToyApollo/Output/prob_14_10.lean:103` private axiom; theorem landings at `:110`, `:134`, `:142`, and `:158`; moments-to-MGF gap remains explicit. | `lake env lean ToyApollo/Output/prob_14_10.lean` passed; global audit passed. |
| 16 | `prob_14_11` | `ToyApollo/Output/prob_14_11.lean`; `phase2_prompt_packs/prob_14_11/proof_obligations.json` | Coupon triangular array debt plus inherited beyond-book exception. | Keep inherited exception separate from non-beyond-book private debts. | `good_corpus_exception_inherited` plus `good_corpus_open_debt_exposed` | `good_corpus_exception_inherited` plus `good_corpus_open_debt_exposed` | Private axioms at `ToyApollo/Output/prob_14_11.lean:60`, `:66`, `:75`, and `:85`; inherited `thm_14_8_ProofBeyondBook` use at `:93` and `:106`; final theorem at `:104`. | `lake env lean ToyApollo/Output/prob_14_11.lean` passed; inherited exception kept separate. |

Validation:

```powershell
lake env lean ToyApollo/Output/thm_14_1.lean
lake env lean ToyApollo/Output/thm_14_2.lean
lake env lean ToyApollo/Output/thm_14_5.lean
lake env lean ToyApollo/Output/thm_14_6.lean
lake env lean ToyApollo/Output/prob_14_6.lean
lake env lean ToyApollo/Output/prob_14_12.lean
lake env lean ToyApollo/Output/thm_14_7.lean
lake env lean ToyApollo/Output/thm_14_8.lean
lake env lean ToyApollo/Output/prob_14_2.lean
lake env lean ToyApollo/Output/ex_14_4_1.lean
lake env lean ToyApollo/Output/ex_14_4_2.lean
lake env lean ToyApollo/Output/ex_14_4_3.lean
lake env lean ToyApollo/Output/prob_14_1.lean
lake env lean ToyApollo/Output/prob_14_8.lean
lake env lean ToyApollo/Output/prob_14_10.lean
lake env lean ToyApollo/Output/prob_14_11.lean
```

## Global Step 4 Validation

Run after each family and once at the end:

```powershell
python -m json.tool docs/phase2_completion_classification.json > $null
python tools/validate_phase2_completion_classification.py
python -m unittest tests.test_phase2_completion_classification
python -m py_compile tools/audit_phase2_clean_debt_surface.py
python -m unittest tests.test_phase2_clean_debt_surface_audit
python tools/audit_phase2_clean_debt_surface.py --write-report --fail-on-errors
```

## Family Status Table

Use this table during execution.

| family | status | notes |
| --- | --- | --- |
| Ch10 convergence / distribution | completed | `prob_10_6` and `prob_10_5` remain `good_corpus_needs_decision`; `prob_10_10_distribution_bridge` and `prob_14_5` recorded as bridge seeds; `thm_10_8` and `ex_10_3_2` reviewed as closed Good Corpus rows. |
| Ch11 estimate | completed | Tier A `prob_11_6` and `prob_11_9` remain `good_corpus_needs_decision`; `prob_11_5` and `prob_11_7` support-return constructors reviewed as theorem-level evidence; private estimate debts remain exposed. |
| Ch13 measure / Fubini | completed | `thm_13_14` remains open debt; `thm_13_12`, `thm_13_13`, and `ex_13_5_1` support-return rows reviewed as closed Good Corpus rows. |
| Ch14 CLT / tightness | completed | Adapter/support checks recorded; `thm_14_8` preserved as the sole beyond-book exception; Lindeberg/Lyapunov/setup private debts and inherited exceptions remain explicitly classified. |

Final Step 4 report must replace `pending` with the final family outcome.
