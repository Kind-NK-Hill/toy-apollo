# Phase2 Interface Bridge Inventory

Created: 2026-05-24
Status: local evidence inventory

## Purpose

This inventory records whether post-Chapter-9 work actually reuses earlier ToyApollo
interfaces, only imports or names them, switches to Mathlib through an explicit bridge,
or re-assumes the same mathematics through private axioms, support packages, setup
fields, or adapters. It is a local evidence inventory only. Step 3 does not modify
Lean files, `proof_obligations.json`, or `project_ledger.json`.

The mandatory Tier A case studies are `prob_10_5`, `prob_10_6`, `prob_11_6`, and
`prob_11_9`, because Step 2.5 classified all four as `needs_decision` rather than
completed theorem reuse.

## Baseline

Preflight files were present for the Step 1/2/2.5 baseline:

- `docs/phase2_completion_classification.json`
- `docs/phase2_completion_classification.md`
- `docs/modification_0525_steps/phase2_step2_5_step1_unfinished_wrapup_plan.md`
- `tools/validate_phase2_completion_classification.py`
- `tests/test_phase2_completion_classification.py`

Preflight validation passed before this inventory was written:

- `python -m json.tool docs/phase2_completion_classification.json > $null`
- `python tools/validate_phase2_completion_classification.py`
- `python -m unittest tests.test_phase2_completion_classification`
- `python tools/audit_phase2_clean_debt_surface.py --fail-on-errors`

`project_ledger.json` had no diff at preflight and is not edited by Step 3.

The repository baseline was dirty before Step 3. No checkpoint commit was created
because the user did not authorize committing. The recorded dirty baseline included
modified Lean files under `ToyApollo/Output`, modified Phase2 audit and prompt-pack
metadata, and untracked Step 1/2/2.5 docs, validation tools, and tests. This inventory
was produced on that uncommitted baseline, and Step 3 only creates this Markdown file.

## Reuse Classes

| class | meaning |
| --- | --- |
| `actual_theorem_reuse` | A downstream task invokes or depends on an earlier theorem with matching mathematical content. |
| `definition_reuse_only` | A downstream task uses earlier names, predicates, or data shapes, but the hard theorem content is not reused. |
| `import_only` | A downstream file imports earlier material but does not use the relevant definitions or theorems as proof content. |
| `mathlib_switch_with_bridge` | The project uses Mathlib objects and includes a local theorem connecting the textbook interface to that Mathlib route. |
| `mathlib_switch_without_bridge` | The project switches to Mathlib objects without a local theorem explaining equivalence to the textbook interface. |
| `reassumed_or_private_axiom` | The downstream result relies on a private axiom, support package, or setup field that re-assumes the missing proof step. |
| `adapter_completed` | A local adapter theorem is present and is an honest bridge for the stated interface, even if the proof route is Mathlib-backed. |
| `needs_decision` | The next action is not mechanical; the project must choose between adding a bridge theorem, rewriting the statement, proving the textbook route, accepting an adapter, or keeping open debt. |

No Tier A outcome is treated as complete merely because the destination file imports
an earlier chapter or because a file name contains `bridge`.

## Summary

| family | main finding | Step 4 input |
| --- | --- | --- |
| A. DCT / convergence | Chapter 7 has Mathlib-backed DCT specializations, but `prob_10_5` needs a theorem from convergence in probability plus domination to mean convergence. That theorem is currently a private axiom. | Decide whether to add a Vitali/subsequence-DCT bridge or rewrite the statement to match existing DCT hypotheses. |
| B. Expectation / integral / moments | Chapter 6 has expectation/integral bridges, but not the moment, measurability, independence, and finite-sum expansion interface needed by `prob_11_6` and `thm_11_7`. | Add moment-interface bridges or keep the affected cases as open proof debt. |
| C. Distribution / weak convergence / countable spaces | `prob_10_6` has the singleton-mass easy direction, but the arbitrary countable singleton-mass-to-distribution theorem is private. Later integer-valued TV work is stronger but specialized. | Build or reject a reusable countable-space bridge. |
| D. Lebesgue-Stieltjes / RS integral | The RS/Stieltjes layer contains useful adapter theorems, but several critical equivalences and examples are axiom-backed. | Split completed adapters from axiom-backed bridges in Step 4 metadata. |
| E. TV distance | `tv_distance_core` proves reusable discrete TV formulas, and `prob_14_5` proves the integer-valued route, but `prob_10_6` is not wired to that route. | Consider a bridge from singleton masses on countable spaces to TV or bounded-test convergence. |
| F. Tightness / CLT / characteristic functions | Chapter 14 is mixed: some real adapters exist, some results are Mathlib-backed with bridges, `thm_14_7` has a private characteristic-expansion axiom, and `thm_14_8` is marked beyond-book. | Preserve adapter wins, and isolate private-axiom or beyond-book cases. |
| G. Chapter 6 probability estimates / occupancy | Chapter 6 has adjacent balls-in-boxes work, but `prob_11_9` needs an empty-box asymptotic model bridge that is not present. | Rewrite `prob_11_9` around a concrete occupancy model or keep it as open math debt. |

## Tier A Case Studies

### `prob_10_5`

| question | finding |
| --- | --- |
| Earlier concept expected to be reusable | Chapter 7 dominated convergence and Chapter 10 convergence in probability. |
| Existing ToyApollo assets | `thm_7_4`, `thm_7_5`, and `thm_7_6` use Mathlib dominated convergence; `ConvergesInProbability` is defined in `ToyApollo/Output/def_10_2.lean:30`; `thm_10_5` proves mean convergence implies probability convergence. |
| Actual downstream use | `ToyApollo/Output/prob_10_5.lean:22` declares `prob_10_5_dominated_probability_to_mean_internal`; `ToyApollo/Output/prob_10_5.lean:32` proves `prob_10_5` from that private axiom. |
| Missing bridge | No theorem connects `ConvergesInProbability` plus domination to the a.e. convergence and domination hypotheses consumed by the Chapter 7 DCT route. |
| Classification | `reassumed_or_private_axiom`, `needs_decision`. |
| Next action | `needs_user_decision`: add a theorem-level Vitali/subsequence-DCT bridge, or rewrite the statement to reuse an existing a.e.-convergence DCT theorem. |

### `prob_10_6`

| question | finding |
| --- | --- |
| Earlier concept expected to be reusable | Distribution convergence on countable spaces from singleton masses, possibly through TV distance. |
| Existing ToyApollo assets | `SingletonMassesConverge` is defined at `ToyApollo/Output/prob_10_6.lean:17`; `CountableSampleBoundedTestFunction` at `ToyApollo/Output/prob_10_6.lean:24`; `prob_10_6_singleton_masses_of_countableSampleDistribution` at `ToyApollo/Output/prob_10_6.lean:36`. |
| Actual downstream use | `ToyApollo/Output/prob_10_6.lean:58` declares `prob_10_6_singleton_masses_to_distribution_internal`; `ToyApollo/Output/prob_10_6.lean:66` uses it to prove `prob_10_6`. |
| Missing bridge | The reverse direction from singleton masses on arbitrary countable spaces to bounded-test distribution convergence is not proved. |
| Classification | `reassumed_or_private_axiom`, `needs_decision`. |
| Next action | `add_bridge_theorem` if a countable-space theorem is desired; otherwise `keep_open_math_debt`. |

### `prob_11_6`

| question | finding |
| --- | --- |
| Earlier concept expected to be reusable | Expectation, integrability, independence, and moment calculations from Chapter 6 and Chapter 11 setup. |
| Existing ToyApollo assets | `textbookIntegral` at `ToyApollo/Output/def_6_7.lean:37`; `expectation` at `ToyApollo/Output/def_6_7.lean:48`; expectation/integral bridges in `ToyApollo/Output/thm_6_7__lemma_1.lean:25`, `:37`, `:52`, and `:59`; `thm_11_3_textbook_expectation_bridge` at `ToyApollo/Output/thm_11_3.lean:67`. |
| Actual downstream use | `ToyApollo/Output/prob_11_6.lean:54` defines sixth-moment support, but `ToyApollo/Output/prob_11_6.lean:62` declares `prob_11_6_sixthMomentSupport_internal`; final theorem at `ToyApollo/Output/prob_11_6.lean:205`. |
| Missing bridge | No theorem derives the needed sixth-moment support from the local random-variable, independence, zero-mean, and boundedness hypotheses. |
| Classification | `definition_reuse_only` for expectation notation; `reassumed_or_private_axiom` and `needs_decision` for the proof step. |
| Next action | `add_bridge_theorem` for moment support or `prove_textbook_route` through explicit finite-sum expansion. |

### `prob_11_9`

| question | finding |
| --- | --- |
| Earlier concept expected to be reusable | Chapter 6 occupancy / balls-in-boxes estimates plus mean-square convergence support. |
| Existing ToyApollo assets | `ex_6_5_2` contains a concrete balls-into-bins model with `ballMeasure` at `ToyApollo/Output/ex_6_5_2.lean:42`, `occupancy` at `:59`, event-cardinality work at `:178`, and theorem `ex_6_5_2` at `:412`. |
| Actual downstream use | `ToyApollo/Output/prob_11_9.lean:33` defines empty-box ratio; `ToyApollo/Output/prob_11_9.lean:40` defines the asymptotic regime; `ToyApollo/Output/prob_11_9.lean:55` declares `prob_11_9_occupancy_moment_calculation_internal`; final theorem at `ToyApollo/Output/prob_11_9.lean:150`. |
| Missing bridge | The Chapter 6 occupancy result is adjacent, but does not provide the empty-box first and second moment asymptotics required by `prob_11_9`. |
| Classification | `definition_reuse_only`, `reassumed_or_private_axiom`, `needs_decision`. |
| Next action | `rewrite_statement_to_reuse_existing_theorem` only if `prob_11_9` is reformulated around an explicit finite occupancy model; otherwise `keep_open_math_debt`. |

## Concept Families

### Family A: DCT / Convergence

Concept name: dominated convergence, convergence in probability, and convergence in
mean. ToyApollo declarations include `thm_7_4`, `thm_7_5`, `thm_7_6`, `thm_7_7`,
`ConvergesInProbability`, and `thm_10_5`. Mathlib corresponding objects include
`MeasureTheory.tendsto_integral_of_dominated_convergence`, `Filter.Tendsto`, and
integrability predicates for Bochner or real integrals.

Bridge or equivalence theorems that actually exist:

- `ToyApollo/Output/thm_7_4.lean:82` declares `thm_7_4`.
- `ToyApollo/Output/thm_7_4.lean:107` uses `MeasureTheory.tendsto_integral_of_dominated_convergence`.
- `ToyApollo/Output/thm_7_5.lean:24` declares `thm_7_5`; `:64` uses Mathlib DCT.
- `ToyApollo/Output/thm_7_6.lean:24` declares `thm_7_6`; `:49` uses Mathlib DCT.
- `ToyApollo/Output/def_10_2.lean:30` defines `ConvergesInProbability`.
- `ToyApollo/Output/thm_10_5.lean:40` and `:57` prove the mean-to-probability direction.

Relation to Step 2/2.5: this family explains why `prob_10_5` stayed `needs_decision`.
The existing DCT theorems are real theorem reuse for a.e. convergence hypotheses, but
not for the probability-convergence interface required by `prob_10_5`.

| downstream task | local declaration | reuse class | evidence | gap | next action |
| --- | --- | --- | --- | --- | --- |
| `thm_7_4`/`thm_7_5`/`thm_7_6` | DCT specializations | `mathlib_switch_with_bridge`, `actual_theorem_reuse` | `ToyApollo/Output/thm_7_4.lean:107`; `ToyApollo/Output/thm_7_5.lean:64`; `ToyApollo/Output/thm_7_6.lean:49` | These are valid DCT routes for their own hypotheses, not for convergence in probability. | `accept_adapter_with_metadata` |
| `thm_10_5` | mean convergence implies probability convergence | `actual_theorem_reuse` | `ToyApollo/Output/thm_10_5.lean:40`; `:57` | Direction is opposite of `prob_10_5`. | Keep as supporting theorem, not Tier A closure. |
| `prob_10_5` | `prob_10_5` | `reassumed_or_private_axiom`, `needs_decision` | `ToyApollo/Output/prob_10_5.lean:22`; `:32` | Missing probability-convergence-to-mean-convergence bridge. | `add_bridge_theorem` or `rewrite_statement_to_reuse_existing_theorem` |

### Family B: Expectation / Integral / Moment Interface

Concept name: textbook expectation, Mathlib integral, integrability, `MemLp`, and
higher moments. ToyApollo declarations include `textbookIntegral`, `expectation`,
`chapter6_expectation_eq_textbookIntegral`, `chapter6_expectation_real_eq_integral`,
`thm_11_3_textbook_expectation_bridge`, `prob_11_6_sixthMomentSupport`, and
`thm_11_7_fourthMomentUniformBound`. Mathlib corresponding objects include
`MeasureTheory.Integrable`, `MeasureTheory.MemLp`, `AEStronglyMeasurable`, and
finite sums of powers.

Bridge or equivalence theorems that actually exist:

- `ToyApollo/Output/def_6_7.lean:37` defines `textbookIntegral`; `:48` defines `expectation`.
- `ToyApollo/Output/thm_6_7.lean:101` derives Mathlib `Integrable` from textbook integrability.
- `ToyApollo/Output/thm_6_7.lean:171` proves `textbookIntegral_eq_some_toRealIntegral`.
- `ToyApollo/Output/thm_6_7.lean:345` proves `textbookIntegrable_realCoe_of_integrable`.
- `ToyApollo/Output/thm_6_7__lemma_1.lean:25`, `:37`, `:52`, and `:59` provide Chapter 6 expectation/integral bridges.
- `ToyApollo/Output/thm_11_3.lean:67` declares `thm_11_3_textbook_expectation_bridge`.

Relation to Step 2/2.5: this family explains why `prob_11_6` and the related
`thm_11_7` moment work are not closed by the existing expectation bridges.

| downstream task | local declaration | reuse class | evidence | gap | next action |
| --- | --- | --- | --- | --- | --- |
| Chapter 6 expectation bridge users | `chapter6_expectation_real_eq_integral` | `actual_theorem_reuse`, `adapter_completed` | `ToyApollo/Output/thm_6_7__lemma_1.lean:59` | Bridge is for expectation/integral equality, not arbitrary moment expansions. | `accept_adapter_with_metadata` |
| `prob_11_6` | `prob_11_6_sixthMomentSupport` | `definition_reuse_only`, `reassumed_or_private_axiom`, `needs_decision` | `ToyApollo/Output/prob_11_6.lean:54`; private axiom at `:62`; final theorem at `:205` | Missing derivation of sixth-moment support and summability from the local hypotheses. | `add_bridge_theorem` or `prove_textbook_route` |
| `thm_11_7` | `thm_11_7_fourthMomentUniformBound` and tail support | `definition_reuse_only`, `reassumed_or_private_axiom` | `ToyApollo/Output/thm_11_7.lean:216`; private axiom at `:244` | Fourth-moment bound exists as a package, but tail summability is re-assumed. | `keep_open_math_debt` unless Step 4 expands this route. |

### Family C: Distribution / Weak Convergence / Countable Sample Spaces

Concept name: countable sample distribution convergence, singleton masses, weak
convergence, and bounded-test convergence. ToyApollo declarations include
`SingletonMassesConverge`, `CountableSampleMeasuresConvergeInDistribution`,
`prob_10_6_singleton_masses_of_countableSampleDistribution`, and later weak/TV
bridges in Chapter 14. Mathlib corresponding objects include probability measures,
push-forward distributions, weak convergence, bounded continuous test functions,
and singleton measurable spaces.

Bridge or equivalence theorems that actually exist:

- `ToyApollo/Output/prob_10_6.lean:17` defines `SingletonMassesConverge`.
- `ToyApollo/Output/prob_10_6.lean:29` defines `CountableSampleMeasuresConvergeInDistribution`.
- `ToyApollo/Output/prob_10_6.lean:36` proves the easy direction from distribution convergence to singleton masses.
- `ToyApollo/Output/prob_10_10_distribution_bridge.lean:21` and `:33` contain actual Problem 10.10 distribution bridge theorems.
- `ToyApollo/Output/thm_14_2.lean:224` declares `thm_14_2_distribution_to_weak`; lines `:331` and `:334` use the weak/CDF equivalence.
- `ToyApollo/Output/prob_14_5.lean:76`, `:180`, `:254`, and `:296` provide integer-valued weak/TV/singleton-mass work.

Relation to Step 2/2.5: this family explains why `prob_10_6` stayed `needs_decision`
even though later Chapter 14 files prove related, more specialized results.

| downstream task | local declaration | reuse class | evidence | gap | next action |
| --- | --- | --- | --- | --- | --- |
| `prob_10_6` easy direction | `prob_10_6_singleton_masses_of_countableSampleDistribution` | `actual_theorem_reuse` | `ToyApollo/Output/prob_10_6.lean:36` | Only proves distribution implies singleton-mass convergence. | Keep as supporting theorem. |
| `prob_10_6` final direction | `prob_10_6_singleton_masses_to_distribution_internal` | `reassumed_or_private_axiom`, `needs_decision` | `ToyApollo/Output/prob_10_6.lean:58`; final theorem at `:66` | Missing arbitrary countable singleton-mass-to-bounded-test bridge. | `add_bridge_theorem` |
| `prob_14_5` | integer-valued weak/TV equivalences | `actual_theorem_reuse`, `mathlib_switch_with_bridge` | `ToyApollo/Output/prob_14_5.lean:76`; `:180`; `:254`; `:296` | Specialized to `ℤ`, not directly reused by `prob_10_6`. | Use as Step 4 model, not as current closure. |

### Family D: Lebesgue-Stieltjes / RS Integral

Concept name: Riemann-Stieltjes integral, Lebesgue-Stieltjes measure, and bridges
between textbook `rsIntegral` notation and Mathlib measure/integral APIs. ToyApollo
declarations include `rsIntegral`, `StieltjesMeasureFunction`, `rsMeasureLocal`,
`RSStieltjesIntegrableOn`, and `lsIntegral_eq_rsIntegral_stieltjesFunction`. Mathlib
corresponding objects include `Measure`, `IntervalIntegrable`, `IntegrableOn`, and
Lebesgue integration against Stieltjes measures.

Bridge or equivalence theorems that actually exist:

- `ToyApollo/Output/def_1_2.lean:28` defines `rsIntegral`; many associated RS algebra facts in that file are axioms.
- `ToyApollo/Output/def_3_5.lean:11` defines `StieltjesMeasureFunction`; `:27` connects to `StieltjesFunction`.
- `ToyApollo/Output/rs_stieltjes_bridge.lean:16` defines `rsMeasureLocal`.
- `ToyApollo/Output/rs_stieltjes_bridge.lean:21` defines `RSStieltjesIntegrableOn`.
- `ToyApollo/Output/rs_stieltjes_bridge.lean:51` and `:62` provide theorem-level integrability adapters.
- `ToyApollo/Output/rs_stieltjes_bridge.lean:117`, `:131`, `:142`, `:147`, `:154`, `:164`, `:174`, `:186`, and `:196` are axiom-backed bridge or example facts.

Relation to Step 2/2.5: this is not a Tier A blocker by itself, but it is the
clearest early-chapter example showing that bridge-file presence is not enough.
Some bridge declarations are completed adapters; other bridge declarations are
axiom-backed.

| downstream task | local declaration | reuse class | evidence | gap | next action |
| --- | --- | --- | --- | --- | --- |
| RS integrability adapters | `rsStieltjesIntegrableOn_of_continuousOn`, `rsStieltjesIntegrableOn_of_bounded_measurableOn_Icc` | `adapter_completed`, `mathlib_switch_with_bridge` | `ToyApollo/Output/rs_stieltjes_bridge.lean:51`; `:62` | The adapters cover integrability, not all RS/LS equality facts. | `accept_adapter_with_metadata` |
| LS/RS equality users | `lsIntegral_eq_rsIntegral_stieltjesFunction` | `reassumed_or_private_axiom` | Axiom at `ToyApollo/Output/rs_stieltjes_bridge.lean:154`; used by `ToyApollo/Output/thm_7_8.lean:19` | Critical equality is bridge-shaped but not proved. | `keep_open_math_debt` or `prove_textbook_route` |
| RS example facts | floor/single-jump/example integrals | `reassumed_or_private_axiom` | `ToyApollo/Output/rs_stieltjes_bridge.lean:131`; `:142`; `:147` | Examples are packaged as axioms. | Keep separated from completed adapters. |

### Family E: TV Distance

Concept name: total variation distance, discrete half-sum formulas, singleton masses,
and weak convergence. ToyApollo declarations include `d_TV`,
`discrete_totalVariationDistance_eq_half_tsum_abs`,
`d_TV_toReal_eq_totalVariationDistance`, and the `prob_14_5` integer-valued TV
theorems. Mathlib corresponding objects include `MeasureTheory.totalVariation`,
PMFs, countable sums, and probability measures.

Bridge or equivalence theorems that actually exist:

- `ToyApollo/Output/tv_distance_core.lean:11` defines `d_TV`.
- `ToyApollo/Output/tv_distance_core.lean:205` proves `discrete_totalVariationDistance_eq_half_tsum_abs`.
- `ToyApollo/Output/tv_distance_core.lean:252` proves `d_TV_toReal_eq_totalVariationDistance` for `ℕ`.
- `ToyApollo/Output/tv_distance_core.lean:449` proves a continuous TV formula.
- `ToyApollo/Output/prob_14_5.lean:100` proves the TV half-sum formula on `ℤ`.
- `ToyApollo/Output/prob_14_5.lean:180` proves singleton masses to TV on `ℤ`.
- `ToyApollo/Output/prob_14_5.lean:254` proves TV to weak convergence on `ℤ`.

Relation to Step 2/2.5: this family is the most promising reuse path for `prob_10_6`,
but the current `prob_10_6` proof does not use this route.

| downstream task | local declaration | reuse class | evidence | gap | next action |
| --- | --- | --- | --- | --- | --- |
| `prob_14_5` | integer-valued TV/weak equivalences | `actual_theorem_reuse`, `adapter_completed` | `ToyApollo/Output/prob_14_5.lean:100`; `:180`; `:254`; `:296` | Works on `ℤ`, not arbitrary countable `Ω`. | `accept_adapter_with_metadata` |
| `prob_10_6` | arbitrary countable bounded-test convergence | `definition_reuse_only`, `reassumed_or_private_axiom`, `needs_decision` | Private axiom at `ToyApollo/Output/prob_10_6.lean:58` | No bridge from `tv_distance_core` PMF theorem to this interface. | `add_bridge_theorem` |
| Future countable bridge | PMF half-sum theorem | `actual_theorem_reuse` as a candidate input | `ToyApollo/Output/tv_distance_core.lean:205` | Needs conversion between `Measure Ω`, PMF, singleton masses, and bounded tests. | Use as a Step 4 proof component. |

### Family F: Tightness / CLT / Characteristic Functions

Concept name: tightness, weak convergence, characteristic functions, Levy continuity,
and CLT routes. ToyApollo declarations include `def_14_3_of_mathlibTight`,
`def_14_3_to_mathlibTight`, `thm_14_1_weak_iff_characteristic`,
`thm_14_5_of_uniformTailBound`, `thm_14_6`, `thm_14_7`, `thm_14_8`, and
`ex_14_4_3`. Mathlib corresponding objects include tight measure sets, weak
convergence of probability measures, characteristic functions, and CLT theorem
packages.

Bridge or equivalence theorems that actually exist:

- `ToyApollo/Output/def_14_3.lean:83` proves `def_14_3_of_mathlibTight`; `:154` proves `def_14_3_to_mathlibTight`; `:203` proves `def_14_3_intervalMathlibTightBridge`.
- `ToyApollo/Output/thm_14_1.lean:127` declares `thm_14_1_weak_iff_characteristic`; `:176` uses Mathlib tightness from characteristic-function convergence.
- `ToyApollo/Output/thm_14_5.lean:334` declares `thm_14_5_of_uniformTailBound`; `:430` declares `thm_14_5`; `:437` and `:442` use Mathlib tightness plus the local adapter.
- `ToyApollo/Output/thm_14_6.lean:200`, `:240`, `:359`, `:459`, and `:487` contain the tight subsequence and characteristic-limit route.
- `ToyApollo/Output/thm_14_7.lean:226` declares `thm_14_7_quadratic_characteristic_expansion_internal`; final theorem at `:261`.
- `ToyApollo/Output/thm_14_8.lean:175`, `:184`, and `:195` expose theorem routes through `thm_14_8_ProofBeyondBook`.
- `ToyApollo/Output/ex_14_4_3.lean:374` declares `ex_14_4_3_lyapunov_condition_internal`; final theorem at `:394`.

Relation to Step 2/2.5: this family is not one uniform debt category. Some files are
Mathlib-backed adapters that should be accepted with metadata; others remain private
axiom or beyond-book exceptions.

| downstream task | local declaration | reuse class | evidence | gap | next action |
| --- | --- | --- | --- | --- | --- |
| `thm_14_5` | tightness from uniform tail bound | `adapter_completed`, `mathlib_switch_with_bridge` | `ToyApollo/Output/thm_14_5.lean:334`; `:430`; `:437`; `:442`; adapter at `ToyApollo/Output/def_14_3.lean:83` | Bridge is local and explicit. | `accept_adapter_with_metadata` |
| `thm_14_6` | characteristic-limit/tight-subsequence route | `mathlib_switch_with_bridge`, `actual_theorem_reuse` | `ToyApollo/Output/thm_14_6.lean:200`; `:240`; `:359`; `:459`; `:487` | Relies on the local Ch14 route, not a Tier A closure issue. | `accept_adapter_with_metadata` |
| `thm_14_7` | Lindeberg-Levy setup | `reassumed_or_private_axiom`, `needs_decision` | Private axiom at `ToyApollo/Output/thm_14_7.lean:226`; theorem at `:261` | Quadratic characteristic expansion is re-assumed. | `keep_open_math_debt` or `prove_textbook_route` |
| `thm_14_8` and `ex_14_4_3` | Lyapunov/Lindeberg CLT route | `mathlib_switch_without_bridge` for beyond-book package; `reassumed_or_private_axiom` for example support | `ToyApollo/Output/thm_14_8.lean:175`; `:184`; `:195`; `ToyApollo/Output/ex_14_4_3.lean:374`; `:394` | `thm_14_8_ProofBeyondBook` is an explicit exception; `ex_14_4_3` also has private Lyapunov support. | `accept_adapter_with_metadata` for beyond-book exception, isolate private debt. |

### Family G: Chapter 6 Probability Estimates / Occupancy

Concept name: Chapter 6 probability estimates, occupancy, balls-in-boxes models,
and empty-box asymptotics. ToyApollo declarations include `prob_6_3`, `ballMeasure`,
`occupancy`, `singleBinCount`, `ex_6_5_2`, `prob_11_9_emptyBoxRatio`, and
`prob_11_9_asymptoticRegime`. Mathlib corresponding objects include finite
probability spaces, counting measures, finite sums, indicators, variance/second
moment calculations, and convergence in mean square.

Bridge or equivalence theorems that actually exist:

- `ToyApollo/Output/ex_6_5_2.lean:42` defines `ballMeasure`.
- `ToyApollo/Output/ex_6_5_2.lean:59` defines `occupancy`.
- `ToyApollo/Output/ex_6_5_2.lean:66` defines the one-bin exact-one-ball event.
- `ToyApollo/Output/ex_6_5_2.lean:178` proves event-cardinality work for the exact-one-ball event.
- `ToyApollo/Output/ex_6_5_2.lean:270` proves integrability of a single-bin indicator.
- `ToyApollo/Output/ex_6_5_2.lean:396` defines `singleBinCount`; `:412` declares theorem `ex_6_5_2`.
- `ToyApollo/Output/prob_6_3.lean:264` declares `prob_6_3`.
- `ToyApollo/Output/prob_11_9.lean:33` defines `prob_11_9_emptyBoxRatio`; `:40` defines the asymptotic regime.

Relation to Step 2/2.5: this family explains why `prob_11_9` is not direct reuse of
Chapter 6. The existing occupancy result proves an adjacent exact-one-ball expectation
statement, not the empty-box mean-square asymptotic statement.

| downstream task | local declaration | reuse class | evidence | gap | next action |
| --- | --- | --- | --- | --- | --- |
| `ex_6_5_2` | concrete occupancy exact-one-ball result | `actual_theorem_reuse` within Chapter 6 | `ToyApollo/Output/ex_6_5_2.lean:42`; `:59`; `:178`; `:412` | Result is adjacent but not empty-box asymptotics. | Keep as possible model source. |
| `prob_11_9` | empty-box ratio and mean-square support | `definition_reuse_only`, `reassumed_or_private_axiom`, `needs_decision` | `ToyApollo/Output/prob_11_9.lean:33`; `:40`; private axiom at `:55`; final theorem at `:150` | No bridge from Ch6 occupancy definitions to required moment calculation. | `rewrite_statement_to_reuse_existing_theorem` or `keep_open_math_debt` |
| `prob_6_3` | Chapter 6 probability estimate | `definition_reuse_only` for this Step 3 inventory | `ToyApollo/Output/prob_6_3.lean:264` | Not an empty-box occupancy theorem for `prob_11_9`. | Do not count as closure for Tier A. |

## Cross-Cutting Findings

- Import presence is not theorem reuse. The useful label for such cases remains `import_only`, but the Tier A blockers are stronger than import-only cases because they contain private axioms or unsupported setup packages.
- Bridge-file presence is not theorem reuse. `rs_stieltjes_bridge.lean` contains both completed adapter theorems and axiom-backed bridge facts.
- Mathlib-backed adapter status is not failure. `thm_7_4` through `thm_7_6`, `def_14_3`, `thm_14_5`, and parts of `thm_14_6` should be recorded as valid `mathlib_switch_with_bridge` or `adapter_completed` where their hypotheses match.
- The Tier A tasks failed at interface boundaries, not at simple naming reuse. Each needs either a new bridge theorem, a statement rewrite, or an explicit decision to keep open debt.
- The strongest Step 4 reuse seed is the TV/countable path, because `tv_distance_core` and `prob_14_5` already contain concrete theorem material even though they do not yet close `prob_10_6`.

## Recommended Step 4 Inputs

1. `prob_10_6` countable distribution / TV bridge. Start from `tv_distance_core.lean:205` and `prob_14_5.lean:180`, then decide whether to generalize from `ℤ` to arbitrary countable `Ω` or rewrite `prob_10_6` to a supported interface.
2. `prob_11_6` moment and integrability interface. Decide whether to prove a sixth-moment support theorem from the current hypotheses or expose the support assumptions explicitly as open math debt.
3. `prob_10_5` convergence-in-probability to mean convergence. Decide between a Vitali/subsequence-DCT bridge and a statement rewrite to a.e. convergence so existing Chapter 7 DCT theorems can be reused.
4. `prob_11_9` occupancy model. Either rewrite around the concrete Chapter 6 finite occupancy model or keep the current abstract empty-box moment calculation as open debt.
5. Chapter 14 adapter/debt cleanup. Preserve `def_14_3`, `thm_14_5`, and the completed `thm_14_6` route as adapter-backed wins, while separating `thm_14_7`, `thm_14_8`, and `ex_14_4_3` debt/exception categories.
6. RS/Stieltjes metadata cleanup. Mark completed adapter theorems separately from axiom-backed RS/LS equivalences and examples.

The optional audit helper was not created in Step 3. The evidence needed here is
semantic and declaration-level; a mechanical tool would only reproduce grep hints and
would not decide whether a theorem actually matches a downstream interface.

## Validation

Preflight validation passed before writing this file:

- classification JSON parsed successfully;
- `tools/validate_phase2_completion_classification.py` passed;
- `tests.test_phase2_completion_classification` passed;
- `tools/audit_phase2_clean_debt_surface.py --fail-on-errors` reported `error_task_count: 0`;
- `project_ledger.json` had no diff.

Final Step 3 validation passed after the Markdown write:

- `rg -n "actual_theorem_reuse|definition_reuse_only|import_only|reassumed_or_private_axiom|needs_decision" docs/modification_0525_steps/phase2_interface_bridge_inventory.md`
- `rg -n "prob_10_5|prob_10_6|prob_11_6|prob_11_9" docs/modification_0525_steps/phase2_interface_bridge_inventory.md`
- `python tools/audit_phase2_clean_debt_surface.py --fail-on-errors`

The audit result remained `error_task_count: 0`. `project_ledger.json` still has no
diff in Step 3, and the only Step 3 file created is this inventory Markdown.
