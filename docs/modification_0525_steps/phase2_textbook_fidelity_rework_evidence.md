# Phase2 Textbook Fidelity Rework Evidence

Created: 2026-05-23
Status: rework evidence

This note records the rework conclusion from the Phase2/proof-debt discussion. It
is intentionally evidence driven: build success, ledger cleanliness, and audit
cleanliness are useful signals, but they are not enough to decide whether a file
has formalized the textbook proof.

## Rework Objective

The real target is not just:

- the Lean file builds;
- the public theorem has no `Support` or `Spine` parameter;
- the ledger/audit looks clean.

The real target is:

1. the Lean file builds;
2. the theorem statement is faithful to the textbook task;
3. the proof body is honestly classified by proof route;
4. bridge/equivalence files connect textbook objects to Mathlib objects;
5. bridge/equivalence theorems do not hide unfinished textbook proofs;
6. `Support`/`Spine`/obligation tracking helps preserve the source proof route,
   rather than becoming metadata-only cleanup.

## Corrected Acceptance Classes

Every important output theorem should be classified into one of these classes.

### `textbook_proof_completed`

The statement is textbook-facing, and the proof body follows the textbook proof
route at theorem/lemma level. Mathlib may still be used for local facts, but it
does not replace the main source proof.

### `mathlib_backed_adapter_completed`

The statement is textbook-facing, but the proof is mainly a specialization or
adapter around a stronger Mathlib theorem. This is valid Lean work, but it is not
the same as formalizing the textbook proof.

### `interface_bridge_completed`

The file proves an equivalence, translation, or compatibility theorem between a
ToyApollo textbook object and a Mathlib object. This is not proof debt by itself.
It becomes a problem only if it silently stands in for an unproved source proof.

### `open_math_debt`

The file still depends on an axiom, a public `Support`/`Spine`/`Bridge`
parameter, a `ProofBeyondBook` package, or an added mathematical assumption that
substitutes for a missing proof step.

### `metadata_only_cleanliness`

The ledger or audit says the task is clean, but the Lean proof route has not been
classified honestly. This class should not count as mathematical completion.

## Evidence From Current ToyApollo Files

### DCT in Chapter 7

Files checked:

- `ToyApollo/Output/thm_7_4.lean`
- `ToyApollo/Output/thm_7_5.lean`
- `ToyApollo/Output/thm_7_6.lean`
- `ToyApollo/Output/thm_7_7.lean`

Concrete evidence:

- `ToyApollo/Output/thm_7_4.lean:82` defines `thm_7_4`.
- `ToyApollo/Output/thm_7_4.lean:107` closes it through
  `MeasureTheory.tendsto_integral_of_dominated_convergence`.
- `ToyApollo/Output/thm_7_5.lean:24` defines `thm_7_5`.
- `ToyApollo/Output/thm_7_5.lean:64` also uses
  `MeasureTheory.tendsto_integral_of_dominated_convergence`.
- `ToyApollo/Output/thm_7_6.lean:24` defines `thm_7_6`.
- `ToyApollo/Output/thm_7_6.lean:49` uses
  `MeasureTheory.tendsto_integral_of_dominated_convergence`.
- `ToyApollo/Output/thm_7_7.lean:6` defines `thm_7_DCT_filter`.
- `ToyApollo/Output/thm_7_7.lean:15` uses
  `tendsto_integral_filter_of_dominated_convergence`.

Conclusion:

The current Chapter 7 DCT output is best classified as
`mathlib_backed_adapter_completed`, not `textbook_proof_completed`. It is a
valid Lean specialization of Mathlib DCT under textbook-facing names, but it does
not demonstrate that the textbook DCT proof route itself has been formalized.

Practical consequence:

If a later theorem uses DCT, the default should be to use the current Chapter 7
DCT theorem when the statement interface matches. If the later proof is written
in a Mathlib form, add a small bridge theorem between the Chapter 7 DCT statement
and the needed Mathlib form. Do not pretend this bridge proves the textbook DCT
route.

### `thm_14_5`

Files checked:

- `ToyApollo/Output/thm_14_5.lean`
- `ToyApollo/Output/def_14_3.lean`

Concrete evidence:

- `ToyApollo/Output/thm_14_5.lean:328` defines
  `thm_14_5_uniformTailBound`.
- `ToyApollo/Output/thm_14_5.lean:334` defines
  `thm_14_5_of_uniformTailBound`.
- `ToyApollo/Output/thm_14_5.lean:371` defines
  `thm_14_5_SourceProofSpine`.
- `ToyApollo/Output/thm_14_5.lean:430` defines public theorem `thm_14_5`.
- `ToyApollo/Output/thm_14_5.lean:437` proves it through Mathlib
  `isTightMeasureSet_of_tendsto_charFun`.
- `ToyApollo/Output/thm_14_5.lean:442` converts the Mathlib tightness result
  through `def_14_3_of_mathlibTight`.
- `ToyApollo/Output/def_14_3.lean:83` defines the bridge theorem
  `def_14_3_of_mathlibTight`.

Conclusion:

The current public `thm_14_5` is `mathlib_backed_adapter_completed`, plus an
`interface_bridge_completed` step through `def_14_3_of_mathlibTight`.

The file also contains a textbook-route skeleton:

- `thm_14_5_uniformTailBound`;
- `thm_14_5_of_uniformTailBound`;
- `thm_14_5_SourceProofSpine`.

But the public theorem does not currently finish the source proof through that
spine. If the acceptance target is textbook proof fidelity, the remaining work
is to prove the source steps feeding `thm_14_5_uniformTailBound` and make the
public theorem assemble through `thm_14_5_of_uniformTailBound`.

For `thm_14_5`, the required classification is therefore not "bad" or "good".
It is:

- current status: `mathlib_backed_adapter_completed`;
- not yet: `textbook_proof_completed`;
- upgrade path: prove the source spine obligations and route public `thm_14_5`
  through the local uniform-tail theorem.

### Chapter 1-8 Is Also Mixed

The evidence does not support the claim that all Chapter 1-8 files already meet
a strict textbook-proof standard.

Examples of theorem-level local work:

- `ToyApollo/Output/thm_6_7.lean:444` defines `thm_6_7`.
- `ToyApollo/Output/thm_6_7.lean:498` defines `thm_6_7_complex`.
- `ToyApollo/Output/tv_distance_core.lean:205` proves
  `discrete_totalVariationDistance_eq_half_tsum_abs`.
- `ToyApollo/Output/tv_distance_core.lean:252` proves
  `d_TV_toReal_eq_totalVariationDistance`.
- `ToyApollo/Output/tv_distance_core.lean:449` proves
  `continuous_totalVariationDistance_eq_half_integral_abs`.

Examples of Mathlib-backed or bridge/debt style work inside early output:

- `ToyApollo/Output/thm_2_3.lean:9` proves the result by using Mathlib
  `measure_union_le`.
- `ToyApollo/Output/rs_stieltjes_bridge.lean:117` declares
  `rsIntegrable_of_bounded_finite_discontinuities` as an axiom.
- `ToyApollo/Output/rs_stieltjes_bridge.lean:131` declares
  `rsIntegral_singleJumpStep_exists` as an axiom.
- `ToyApollo/Output/rs_stieltjes_bridge.lean:142` declares
  `rsIntegral_floor_square_0_10` as an axiom.
- `ToyApollo/Output/rs_stieltjes_bridge.lean:154` declares
  `lsIntegral_eq_rsIntegral_stieltjesFunction` as an axiom.
- `ToyApollo/Output/cantor_distribution_bridge.lean:12` and nearby lines
  declare `cantorBridgeP`, `cantorBridge_isProbability`, independence, series,
  interval probability, and Cantor-set facts as axioms.

Conclusion:

"Chapter 1-8 level" cannot honestly mean "every theorem has a fully formalized
textbook proof body." The actual Chapter 1-8 corpus is mixed:

- some files contain real theorem-level local proofs;
- some files are Mathlib-backed adapters;
- some bridge files intentionally use axioms;
- some bridge files encode compatibility work rather than textbook proof work.

The useful standard is therefore not "make post-Ch9 look like an imagined pure
Chapter 1-8." The useful standard is "classify proof route honestly and avoid
public hidden assumptions."

### Post-Ch9 Interface and Debt Examples

Files checked:

- `ToyApollo/Output/prob_10_5.lean`
- `ToyApollo/Output/thm_9_5.lean`
- `ToyApollo/Output/thm_10_8.lean`
- `ToyApollo/Output/thm_14_8.lean`

Concrete evidence after the 2026-05-23 rework:

- `ToyApollo/Output/prob_10_5.lean` defines public theorem `prob_10_5` without
  the former public `h_dominated_bridge` parameter.
- The missing dominated-convergence-in-probability to mean-convergence route is
  now isolated in private axiom
  `prob_10_5_dominated_probability_to_mean_internal`, so the task is still
  `open_math_debt`, not `textbook_proof_completed`.
- `ToyApollo/Output/thm_9_5.lean:288` defines
  `CharacteristicInversionSourceSpine`.
- `ToyApollo/Output/thm_9_5.lean:348` defines public theorem `thm_9_5`.
- `ToyApollo/Output/thm_10_8.lean:101` defines
  `mkSkorokhodQuantileSupport`.
- `ToyApollo/Output/thm_10_8.lean:115` defines public theorem `thm_10_8`.
- `ToyApollo/Output/thm_10_8.lean:123` constructs support internally through
  `mkSkorokhodQuantileSupport`.
- `ToyApollo/Output/thm_14_8.lean:167` defines
  `thm_14_8_ProofBeyondBook`.

Conclusion:

- `prob_10_5` is still `open_math_debt`, because the substantial bridge/proof
  is private axiom debt; however the public theorem no longer exports that debt
  as a caller parameter.
- `thm_9_5` shows the intended pattern: a source spine may exist internally, but
  the public theorem should not expose the spine as a user obligation.
- `thm_10_8` shows a cleanup pattern: support is constructed internally rather
  than required as a public parameter.
- `thm_14_8_ProofBeyondBook` remains the only intended beyond-book exception.

## Current Rework Progress Snapshot

The 2026-05-23 implementation pass cleaned the P0 and P1 public proof-package
interfaces while keeping unproved mathematics classified as `open_math_debt`.

Public-interface debts internalized as private axioms:

- `prob_10_5_dominated_probability_to_mean_internal`;
- `prob_10_6_singleton_masses_to_distribution_internal`;
- `prob_11_6_sixthMomentSupport_internal`;
- `prob_11_8_covarianceDecaySupport_internal`;
- `prob_11_9_occupancy_moment_calculation_internal`;
- `prob_11_10_continuous_grid_uniformization_internal`;
- `prob_14_1_stirling_cdf_convergence_internal`;
- `ex_14_4_1_apply_lindeberg_levy_clt_internal`;
- `ex_14_4_2_apply_lindeberg_levy_clt_internal`;
- `prob_14_2_apply_lindeberg_levy_clt_internal`;
- `prob_14_8_mgf_to_characteristic_convergence_internal`;
- `prob_14_10_moments_to_mgf_setup_internal`;
- `ex_14_4_3_lyapunov_condition_internal`;
- `prob_14_11_generalized_triangular_array_internal`;
- `prob_14_11_mean_asymptotic_internal`;
- `prob_14_11_variance_asymptotic_internal`;
- `prob_14_11_generalized_lyapunov_condition_internal`;
- `thm_14_7_quadratic_characteristic_expansion_internal`;
- `thm_11_7_tail_summability_internal`;
- `thm_13_14_conditional_expectation_internal`.

`prob_10_6` was corrected further on 2026-05-24. The earlier post-cleanup
real-line common-countable-support statement was not a faithful replacement for
the textbook countable sample-space theorem: weak/CDF convergence on `ℝ` plus a
common countable support does not force singleton-mass convergence at atoms. The
public theorem now uses an abstract countable sample-space interface,
`CountableSampleMeasuresConvergeInDistribution`, formulated through bounded
measurable test functions. The bounded-test-to-singleton direction now has a
theorem-level landing, `prob_10_6_singleton_masses_of_countableSampleDistribution`,
by testing against the singleton indicator. The result remains
`open_math_debt` because the reverse singleton-mass-to-bounded-test direction is
still supplied by `prob_10_6_singleton_masses_to_distribution_internal`.

`prob_11_8` was reviewed for the next proof-replacement step. The public theorem
no longer exposes a covariance-decay support package; it calls a private axiom
for the AR(1)-to-covariance-decay calculation. The downstream use of Problem
11.7 is already theorem-level through
`prob_11_7_sampleMeanVarianceSupport_of_covarianceDecay` and `prob_11_7`. The
remaining `prob_11_8` debt is narrower: establish local AR(1) second-moment,
variance-bound, and covariance-recursion/geometric-decay landings without
turning them into public proof-package fields.

The `thm_14_6` interval-tightness bridge is now theorem-level evidence:
`def_14_3_to_mathlibTight` proves the interval-to-Mathlib direction, and
`def_14_3_intervalMathlibTightBridge` packages both directions.  The public
helper `thm_14_6_of_interval_tight` no longer exposes an `hbridge` parameter.

`prob_14_7` is classified as `textbook_proof_completed` at the law-level
interface. Its public setup fields are source/object assumptions, while the
product-limit and final Levy steps now point to theorem-level Lean landings:
`prob_14_7_sum_characteristic_convergence`, `prob_14_7_sum_laws_converge`, and
`prob_14_7`.

`prob_14_2` no longer exposes the CLT proof package through public setup fields
such as `cltSetup` and `clt_standardizedLaws`. The Gamma summation and
standardization pieces remain public theorem/definition evidence; the missing
Lindeberg-Levy specialization is private open debt in
`prob_14_2_apply_lindeberg_levy_clt_internal`.

The same CLT proof-package cleanup was applied to `ex_14_4_1` and
`ex_14_4_2`. Their public setup structures now keep the Bernoulli/binomial and
Poisson source objects, while the missing Theorem 14.7 specializations are
private open debt in `ex_14_4_1_apply_lindeberg_levy_clt_internal` and
`ex_14_4_2_apply_lindeberg_levy_clt_internal`.

`prob_14_3`, `prob_14_4`, and `prob_14_9` were manually reviewed as source setup
cases. Their public setup structures carry task objects and hypotheses rather
than proof packages, and their main proof steps land on theorem-level
declarations in the corresponding files.

`ex_14_3_1` and `ex_14_3_2` were also reviewed as source setup cases. Their
setup structures carry law objects and characteristic-function formulas, while
the pointwise characteristic limits and final distribution-convergence steps
are theorem-level Lean declarations.

`ex_10_3_2`'s Gaussian special-case metadata no longer uses
`ex_10_3_2_GaussianDensityConvergenceSetup` as a proof landing. The active
landing now points to theorem-level Gaussian density probability, pointwise
density convergence, and distribution-convergence declarations; the setup
structure remains source parameter data.

`thm_14_7` remains `open_math_debt`: `quadratic_expansion` has been internalized
as `thm_14_7_quadratic_characteristic_expansion_internal`, but the public setup
still carries the characteristic-product route through `c_definition`,
`c_limit`, and `standardNormal_characteristic`.

The remaining `public_proof_package_return_review` findings were manually
reviewed on 2026-05-24. None of the reviewed tasks exposes a
`Support`/`Spine`/`Bridge` package as a final public theorem argument. The
findings are syntactic review signals for internal theorem-level evidence or for
already-internalized open math debt. Concrete examples:

- `prob_11_7_sampleMeanVarianceSupport_of_covarianceDecay` constructs
  `prob_11_7_sampleMeanVarianceSupport` internally from covariance-decay
  assumptions; the proof-obligation discharge metadata now points to that
  theorem-level landing.
- `thm_13_13_atomIntegral_from_jointLaw` constructs
  `thm_13_13_atomIntegralSupport` internally, and the public theorem
  `thm_13_13` calls it rather than requiring the caller to provide support.
- `prob_11_10`, `prob_11_6`, `prob_11_9`, `thm_13_14`, and `ex_14_4_3` still
  contain real open mathematics, but those obligations are private/internalized
  debt rather than public proof-package parameters.

Latest clean-debt audit result:

- `error_task_count: 0`;
- no `public_proof_package_parameter` findings;
- no `public_interface_bridge_parameter_review` findings;
- remaining findings are review-only public setup/return classifications and
  the allowed/inherited `thm_14_8_ProofBeyondBook` exception.

The 2026-05-24 continuation also synchronized stale mirror and prompt-pack
candidate files for the current P0/P1 cleanup state.  The `output_lean_files`
mirrors for `prob_10_5`, `prob_10_6`, `prob_11_6`, `prob_11_8`, `prob_11_9`,
`prob_11_10`, `thm_11_7`, `thm_13_14`, `thm_14_6`, and `ex_14_4_3` now match
their corresponding `ToyApollo/Output` files.  The `prob_10_5` and `prob_10_6`
prompt-pack drafts/candidates were also updated so future generation does not
start from the obsolete public `h_dominated_bridge` or `h_countable_bridge`
interfaces.  A mirror-inclusive strict audit now reports `error_task_count: 0`;
before this synchronization it reported 20 mirror-only public proof-package
errors.

## Evidence From Tao's Analysis Formalization

Local reference roots checked:

- `D:/Grad_Study/Practimum/Formalization/_external_refs/teorth-analysis-files`
- `D:/Grad_Study/Practimum/Formalization/_external_refs/tao_analysis_reference`

Concrete evidence:

- `_external_refs/teorth-analysis-files/README.md:5` says exercises left to the
  reader are represented as `sorry`, and the repository does not intend to place
  solutions directly.
- `_external_refs/teorth-analysis-files/README.md:9` states that the
  formalization gradually transitions from textbook-provided definitions to
  Mathlib-provided definitions as the text progresses.
- `_external_refs/teorth-analysis-files/Analysis/Section_5_epilogue.lean:5`
  identifies the file as the Chapter 5 epilogue connecting textbook reals with
  Mathlib reals.
- `_external_refs/teorth-analysis-files/Analysis/Section_5_epilogue.lean:11`
  says `Chapter5.Real` is deprecated from that point onward.
- `_external_refs/teorth-analysis-files/Analysis/Section_5_epilogue.lean:127`
  introduces the isomorphism between `Chapter5.Real` and Mathlib reals.
- `_external_refs/teorth-analysis-files/Analysis/Section_6_epilogue.lean:5`
  identifies the file as connections with Mathlib limits.
- `_external_refs/teorth-analysis-files/Analysis/Section_6_epilogue.lean:35`
  defines `Chapter6.Sequence.tendsto_iff_Tendsto`.
- `_external_refs/tao_analysis_reference/lean-code/Analysis/Section_8_2.lean:25`
  says the local summation notation will be deprecated in favor of Mathlib
  `Summable` and `tsum`.
- `_external_refs/tao_analysis_reference/lean-code/Analysis/Section_8_2.lean:342`
  defines `AbsConvergent'.iff_Summable`.
- `_external_refs/tao_analysis_reference/lean-code/Analysis/Section_8_2.lean:386`
  defines `Sum'.eq_tsum`.

Conclusion:

Tao's code does not set the standard "every textbook proof is fully formalized
before Mathlib is used." The visible standard is:

1. introduce textbook objects where pedagogically useful;
2. write explicit epilogue/bridge/equivalence theorems;
3. transition to Mathlib after the bridge point;
4. mark unfinished exercise-level material with `sorry`;
5. accept some technical changes for Mathlib compatibility.

This is compatible with ToyApollo only if ToyApollo also classifies adapter work
honestly. It is not compatible with labeling every Mathlib-backed adapter as a
completed textbook proof.

## What Went Wrong In The Phase2 Discussion

The earlier discussion blurred three different goals:

1. Lean build success;
2. public interface hygiene;
3. textbook proof fidelity.

The new Phase2 mechanism helped with item 2 and with tracking item 3, but it did
not by itself prove item 3. If the ledger/audit treated a file as clean after
only interface cleanup, that was `metadata_only_cleanliness`.

The old Phase2 looked more effective for Chapter 1-8 partly because it produced
buildable files with fewer visible scaffolds, but the current evidence shows
that Chapter 1-8 also includes Mathlib-backed adapters and axiom-backed bridge
files. Therefore the old Phase2 was simpler and less intrusive, but it did not
guarantee full textbook proof fidelity either.

## Correct Rework Standard

For current and future review, "Chapter 1-8 level" should be redefined as:

1. the file builds;
2. public theorem statements do not expose artificial `Support`, `Spine`,
   `Bridge`, or `ProofBeyondBook` parameters, except the unique
   `thm_14_8_ProofBeyondBook` exception;
3. theorem statements remain textbook-facing unless there is a documented reason
   to switch to Mathlib form;
4. each major theorem has a proof-route class:
   `textbook_proof_completed`, `mathlib_backed_adapter_completed`,
   `interface_bridge_completed`, or `open_math_debt`;
5. bridge files state exactly what they bridge, and whether they rely on axioms;
6. metadata cannot count as proof unless the Lean landing is an actual
   theorem/lemma with the relevant mathematical content.

## Immediate Consequences

For DCT:

- current Chapter 7 DCT files should be classified as
  `mathlib_backed_adapter_completed`;
- later DCT users may reuse them directly when interfaces match;
- if later statements use a different Mathlib form, add a bridge theorem;
- do not claim the textbook DCT proof route is completed unless the local proof
  route is actually formalized.

For `thm_14_5`:

- current public theorem should be classified as
  `mathlib_backed_adapter_completed`;
- `def_14_3_of_mathlibTight` should be classified as
  `interface_bridge_completed`;
- if the target is textbook fidelity, finish the local
  `thm_14_5_SourceProofSpine` route and prove `thm_14_5_uniformTailBound`;
- then route public `thm_14_5` through `thm_14_5_of_uniformTailBound`.

For post-Ch9 cleanup:

- cleaning public `Support`/`Spine` parameters is necessary but not sufficient;
- open public bridge parameters like `prob_10_5.h_dominated_bridge` are real
  open math debt unless internalized by theorem-level proof;
- `ProofBeyondBook` should remain restricted to `thm_14_8_ProofBeyondBook`;
- the next useful mechanism change is not more debt bureaucracy, but proof-route
  classification attached to actual Lean declarations.

## Work Review

Original failure mode:

- I treated "Chapter 1-8 level" too much as build/interface cleanliness.
- I did not initially separate textbook-proof completion from
  Mathlib-backed-adapter completion.
- I overused mechanism-level explanations where the user was asking for concrete
  evidence from files.

Corrected position:

- Chapter 1-8 is not a pure gold standard of fully formalized textbook proofs.
- Post-Ch9 is not bad merely because the math is later or harder.
- The real problem is unclassified proof route plus public hidden obligations.
- The right rework is to classify each task honestly, clean public artificial
  parameters, and decide explicitly which adapter theorems must be upgraded to
  textbook proof formalizations.

## 2026-05-24 Prompt-Pack Sync Follow-Up

The post-Ch9 rework also requires prompt-pack candidates and mirror files to
match the current Lean outputs. A stale prompt-pack file can reintroduce a
public proof package even after the canonical `ToyApollo/Output` file has been
cleaned.

Follow-up sync work completed on 2026-05-24:

- synchronized current draft/latest candidates for `prob_11_6`, `prob_11_8`,
  `prob_11_9`, `prob_11_10`, `thm_11_7`, `thm_13_14`, `thm_14_5`,
  `thm_14_6`, and `ex_14_4_3` from `ToyApollo/Output`;
- synchronized `thm_14_5` mirrors in `output_lean_files/general` and
  `output_lean_files/chapter14-tightness`;
- refreshed latest candidate hashes in metadata for the synchronized packs;
- corrected metadata summaries so open source-route obligations remain open
  instead of being reported as accepted proof debt.

For `thm_14_5`, the current public theorem is still
`mathlib_backed_adapter_completed`: it proves Definition 14.3 tightness using
Mathlib characteristic-function tightness plus `def_14_3_of_mathlibTight`.
The ten textbook SourceProofSpine obligations remain open and `needs_review`;
only the final adapter bridge is counted as accepted/proved.
