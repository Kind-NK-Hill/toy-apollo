# thm_13_14 Phase2 Repair Report

Task: `thm_13_14`

Result: `textbook_proof_completed`.

## Lean Landings

Reusable bridge files:

- `phase2_measure_eq_withDensity_of_forall_measurable`
- `phase2_setIntegral_withDensity_ofReal_eq`
- `phase2_integrable_withDensity_ofReal_of_weighted`
- `phase2_vectorMeasure_ext_of_Icc`

Task-local theorem-level route:

- `thm_13_14_measure_eq_withDensity`
- `thm_13_14_setIntegral_jointDensity_eq`
- `thm_13_14_integrable_under_jointDensity`
- `thm_13_14_jointDensity_integrable`
- `thm_13_14_kernel_stronglyMeasurable`
- `thm_13_14_gWeighted_abs_integrable`
- `thm_13_14_marginalDensity_pos_of_nonneg_ne_zero`
- `thm_13_14_kernel_abs_mul_marginal_le_integral_abs`
- `thm_13_14_kernelWeighted_integrable_from_gWeighted`
- `thm_13_14_setIntegral_verticalCylinder_prod_symm`
- `thm_13_14_kernel_mul_marginal_eq_integral`
- `thm_13_14_interval_weighted_identity`
- `thm_13_14_interval_fubini_from_joint_density`
- `thm_13_14_piLambdaExtensionSupport_from_integrable`

## Final Assembly

`thm_13_14_isConditionalExpectationVersion` was strengthened so it now records:

- measurability of the candidate kernel;
- integrability of `g(X)`;
- integrability of `h(Y)`;
- the defining set-integral identity on every represented `sigma(Y)` set.

The final theorem `thm_13_14` proves this strengthened predicate internally.
It no longer has public `hIntervals`, `hExtend`, `hKernelWeightedInt`, or any
other Support/Spine/Bridge proof-package premise.

The identity theorem `thm_13_14_identity` is a direct specialization of the
main theorem to `g = fun x => x`; it also has no public identity-kernel
integrability premise.

## Public Assumptions

Remaining public assumptions are source-facing formal spellings:

- `thm_13_14_jointDensityLaw P fXY`;
- `Measurable g`;
- `Measurable fXY`;
- `∀ z, 0 ≤ fXY z`;
- `Integrable (fun z => fXY z * g z.1) volume`, spelling `g(X) in L1(P)` under
  the density law;
- `∀ y, thm_13_14_marginalDensity fXY y ≠ 0`, matching the source
  simplification.

These are not proof packages. The previous candidate-kernel weighted
integrability premise is now derived by
`thm_13_14_kernelWeighted_integrable_from_gWeighted`.

## Validation

- `lake env lean ToyApollo/Output/thm_13_14.lean` passed before metadata update.
- Full task validators are rerun in the final verification pass for this repair.
