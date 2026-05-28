# Chapter 14 Worker D Classification

Created: 2026-05-23
Status: honest classification pass

This note records the Worker D Phase 3/4 classification for the scoped Chapter
14 tasks. It is tied to the current Lean files and proof-obligation metadata,
not to the project ledger. `project_ledger.json` was intentionally not edited.

## Classification Rules Used

- `textbook_proof_completed`: theorem-level Lean proof follows the source route.
- `mathlib_backed_adapter_completed`: public theorem is buildable, but the main
  proof route is a specialization of a stronger Mathlib theorem.
- `interface_bridge_completed`: theorem-level bridge/equivalence is proved.
- `interface_translation_open`: the bridge is an interface translation, but a
  theorem-level bridge direction is still supplied as a public parameter.
- `open_math_debt`: public setup/support/bridge data carries unproved source
  mathematics or a proof package remains open.
- `allowed_beyond_book_exception`: only `thm_14_8_ProofBeyondBook`.

## Task Classifications

| task | current class | evidence | next action |
| --- | --- | --- | --- |
| `thm_14_5` | `mathlib_backed_adapter_completed`; source route open | `ToyApollo/Output/thm_14_5.lean` proves public `thm_14_5` through `isTightMeasureSet_of_tendsto_charFun` and `def_14_3_of_mathlibTight`; it does not assemble through `thm_14_5_SourceProofSpine` or `thm_14_5_of_uniformTailBound`. | Keep adapter classification. The source obligations in `phase2_prompt_packs/thm_14_5/proof_obligations.json` are reopened until theorem-level source-route lemmas exist. |
| `thm_14_6` | `mathlib_backed_adapter_completed`; interval bridge is `interface_bridge_completed` | Main `thm_14_6` uses Mathlib tightness compactness. `def_14_3_to_mathlibTight` proves the interval-to-Mathlib direction, `def_14_3_intervalMathlibTightBridge` packages both directions, and `thm_14_6_of_interval_tight` no longer exposes `hbridge`. | Keep main theorem classified as Mathlib-backed adapter; no public interval bridge parameter remains. |
| `thm_14_7` | `open_math_debt` | Public theorems consume `thm_14_7_LindebergLevySetup`. The unused public `quadratic_expansion` setup field has been removed and isolated in private axiom `thm_14_7_quadratic_characteristic_expansion_internal`; `c_definition`, `c_limit`, and `standardNormal_characteristic` still remain public law-level proof/interface assumptions because removing them without replacement would widen the theorem. | Keep open until centering, independent-sum characteristic convergence, and the normal characteristic identification have theorem-level Lean landings. |
| `thm_14_8` | `allowed_beyond_book_exception` | Source text says the proof is beyond the book; Lean exposes `thm_14_8_ProofBeyondBook`. | Preserve as the only beyond-book exception. |
| `ex_14_3_1` | `textbook_proof_completed` at the law-level interface | `ex_14_3_1_BinomialPoissonSetup` carries source/object data: positive `λ`, the binomial laws, the Poisson target law, and their characteristic-function formulas. The proof route lands in `ex_14_3_1_binomialCharacteristic_tendsto`, `ex_14_3_1_pointwiseCharacteristicConvergence`, `ex_14_3_1_converges_to_poisson`, and `ex_14_3_1`; no private axiom or public proof-field debt is present. | Keep setup public and documented as source/object data. |
| `ex_14_3_2` | `textbook_proof_completed` at the law-level interface | `ex_14_3_2_GeometricExponentialSetup` carries source/object data: positive `λ`, scaled geometric laws, exponential target law, and characteristic-function formulas. The proof route lands in `ex_14_3_2_scaledGeometricCharacteristic_tendsto`, `ex_14_3_2_pointwiseCharacteristicConvergence`, `ex_14_3_2_converges_to_exponential`, and `ex_14_3_2`; no private axiom or public proof-field debt is present. | Keep setup public and documented as source/object data. |
| `ex_14_4_1` | `open_math_debt` | The public `ex_14_4_1_BernoulliBinomialSetup` no longer exposes `cltSetup`, `clt_mean`, `clt_sigma_sq`, `clt_standardizedLaws`, or `clt_standardNormalLaw`. The missing Bernoulli/binomial specialization of the Lindeberg-Levy setup is isolated in private axiom `ex_14_4_1_apply_lindeberg_levy_clt_internal`. | Replace the private axiom with theorem-level construction of the `thm_14_7_LindebergLevySetup` from the Bernoulli source data. |
| `ex_14_4_2` | `open_math_debt` | The public `ex_14_4_2_PoissonNormalSetup` no longer exposes `cltSetup`, `clt_mean`, `clt_sigma_sq`, `clt_standardizedLaws`, or `clt_standardNormalLaw`. The Poisson mean/variance and characteristic definitions remain theorem-level evidence; the missing CLT specialization is isolated in private axiom `ex_14_4_2_apply_lindeberg_levy_clt_internal`. | Replace the private axiom with theorem-level construction of the `thm_14_7_LindebergLevySetup` from the Poisson source data. |
| `ex_14_4_3` | `open_math_debt` plus inherited beyond-book exception | Public theorem no longer takes `hLyapunov`; it correctly inherits `thm_14_8_ProofBeyondBook`. The non-beyond-book Lyapunov verification is isolated in private axiom `ex_14_4_3_lyapunov_condition_internal`. | Replace the private axiom with theorem-level fourth-moment/Riemann-sum evidence. |
| `prob_14_1` | `open_math_debt` | Public setup still contains the finite Polya urn mass field because it constrains the task laws and cannot be safely internalized without widening the statement. The Stirling-to-Beta CDF step is no longer public setup data; it is isolated in private axiom `prob_14_1_stirling_cdf_convergence_internal`. Obligations 1 and 4 remain open. | Prove finite urn law and Stirling-to-Beta convergence or keep open. |
| `prob_14_2` | `open_math_debt` | The public `prob_14_2_GammaCLTSetup` no longer exposes `cltSetup`, `clt_mean`, `clt_sigma_sq`, `clt_standardizedLaws`, or `clt_standardNormalLaw`. The Gamma summation and standardization steps have theorem/definition landings, but the construction and application of the Lindeberg-Levy CLT specialization is isolated in private axiom `prob_14_2_apply_lindeberg_levy_clt_internal`. | Replace the private axiom with theorem-level construction of the `thm_14_7_LindebergLevySetup` from the Gamma source data. |
| `prob_14_3` | `textbook_proof_completed` for the law-level counterexample | `prob_14_3_GaussianVarianceEscapeSetup` contains only the Gaussian laws and their characteristic-law hypothesis. The proof route lands in `prob_14_3_gaussian_characteristic_limit`, `prob_14_3_tight_to_limitCharacteristic`, `prob_14_3_not_weakLimit`, `prob_14_3_not_tight`, and `prob_14_3`; no public proof-field debt is present. | Keep setup public and documented as source/object data. |
| `prob_14_4` | `textbook_proof_completed` at the law-level interface | `prob_14_4_ShrinkingGaussianSetup` contains only the shrinking Gaussian laws and their characteristic-law hypothesis. The convergence route lands in `prob_14_4_gaussian_characteristic_limit`, `prob_14_4_converges_to_dirac_zero`, `prob_14_4_limit_is_dirac_zero_characteristic`, and `prob_14_4`. | Keep setup public and documented as source/object data. |
| `prob_14_7` | `textbook_proof_completed` at the law-level interface | The public setup fields are source/object assumptions: law convergence and convolution identities encoding independence. The theorem-level route is closed by `prob_14_7_distribution_convergence_to_characteristic`, `prob_14_7_independent_sum_characteristic`, `prob_14_7_target_sum_characteristic`, `prob_14_7_sum_characteristic_convergence`, `prob_14_7_sum_laws_converge`, and `prob_14_7`. | Keep setup assumptions public; no private proof-field debt remains for this law-level statement. |
| `prob_14_8` | `open_math_debt` | The public setup no longer carries `mgf_to_characteristic_convergence`; obligation 4 is isolated in private axiom `prob_14_8_mgf_to_characteristic_convergence_internal`. The remaining public setup fields are the source hypotheses: laws, target law, a positive neighborhood, MGF existence, and pointwise MGF convergence on that neighborhood. | Replace the private axiom with a theorem-level MGF-to-characteristic convergence route. |
| `prob_14_9` | `textbook_proof_completed` for the law-level continuous-mapping theorem | `prob_14_9_ContinuousMappingSetup` carries the natural source hypotheses: source convergence, measurability, push-forward laws, the continuity set, and full target mass. The proof route lands in `prob_14_9_mapped_laws_are_pushforwards`, `prob_14_9_limsup_preimage_closed_le`, `prob_14_9_mapped_laws_converge`, `prob_14_9_mapped_characteristic_convergence`, and `prob_14_9`; no private axiom or public proof-field debt is present. | Keep setup public; consider adding an audit allowlist class for reviewed source setup parameters if the review noise becomes costly. |
| `prob_14_10` | `open_math_debt` | The public setup no longer carries `moments_to_mgf_setup`; obligation 4 is isolated in private axiom `prob_14_10_moments_to_mgf_setup_internal`. The remaining public setup fields are the source objects and bounded-support hypotheses. The forward weak-to-moment direction has theorem-level landing `prob_14_10_weak_convergence_to_moments_under_boundedness`. | Replace the private axiom with a theorem-level bounded moments-to-MGF setup route. |
| `prob_14_11` | `open_math_debt` plus inherited beyond-book exception | Public theorem correctly inherits `thm_14_8_ProofBeyondBook`; non-beyond-book obligations 2, 3, and 4 are no longer public setup proof fields and are isolated in private axioms `prob_14_11_generalized_triangular_array_internal`, `prob_14_11_mean_asymptotic_internal`, `prob_14_11_variance_asymptotic_internal`, and `prob_14_11_generalized_lyapunov_condition_internal`. | Replace those private axioms with theorem-level generalized coupon representation, asymptotic scale, and Lyapunov proofs. |
| `prob_14_12` | mixed: local `textbook_proof_completed` tightness route plus `mathlib_backed_adapter_completed` mean route | The setup fields are source/object assumptions: probability, measurability, push-forward laws, uniform integrability, and convergence in probability. Former proof fields were replaced by theorem-level landings such as `prob_14_12_variable_ui_to_law_ui_of_distributions`, `prob_14_12_markov_tail_uniform_integrability_to_tightness`, and `prob_14_12_uniform_integrability_probability_to_mean`; no private axiom or public proof-field remains in this file. | Keep current setup public and documented. Do not internalize source assumptions; only upgrade the mean-convergence adapter if strict textbook-route formalization is later required. |

## Beyond-Book Boundary

`thm_14_8_ProofBeyondBook` is the only permitted beyond-book exception. Direct
uses in `ex_14_4_3` and `prob_14_11` are inherited exceptions, not ordinary
proved debt. No other Chapter 14 setup, support, spine, or bridge field should
be promoted to `accepted_as_proof_debt`.

## Metadata Changes

- `phase2_prompt_packs/thm_14_5/proof_obligations.json` now classifies the
  public theorem as `mathlib_backed_adapter_completed` and reopens the textbook
  source-route obligations.
- The corresponding `obl_thm_14_5_*` proof-obligation files were reopened for
  the same reason.
- `phase2_prompt_packs/thm_14_6/proof_obligations.json` now records
  `interval_to_mathlib_tight_bridge` as `interface_bridge_completed`.
- `phase2_prompt_packs/prob_14_2/proof_obligations.json` now records
  `apply_lindeberg_levy_clt` as open. The former public CLT setup fields were
  removed, and the remaining debt lands on private axiom
  `prob_14_2_apply_lindeberg_levy_clt_internal`.
- `phase2_prompt_packs/ex_14_4_1/proof_obligations.json` and
  `phase2_prompt_packs/ex_14_4_2/proof_obligations.json` now record their CLT
  specialization steps as open private debt instead of public setup fields.
- `phase2_prompt_packs/prob_14_7/proof_obligations.json` now records theorem
  landings for the product-limit and Levy conclusion steps:
  `prob_14_7_sum_characteristic_convergence`, `prob_14_7_sum_laws_converge`,
  and `prob_14_7`.
- `phase2_prompt_packs/prob_14_12/proof_obligations.json` records that former
  setup-field landings for variable-to-law UI, Markov tightness, and
  UI/probability-to-mean convergence were replaced by theorem-level Lean
  declarations.

The `thm_14_6` bridge classification is backed by new theorem-level Lean proof
landings in `ToyApollo/Output/def_14_3.lean`.
