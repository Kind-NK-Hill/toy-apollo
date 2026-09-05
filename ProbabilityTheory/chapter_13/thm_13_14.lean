/-
TASK ID: thm_13_14
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-continuous-random-variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_13.thm_13_14_support




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ENNReal

noncomputable section



theorem thm_13_14
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hGMeas : Measurable g)
    (hDensityMeas : Measurable fXY)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hGWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * g z.1) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_isConditionalExpectationVersion P g
      (thm_13_14_conditionalExpectationKernel fXY g) :=
  thm_13_14_from_intervalFubini_piLambda P fXY g
    hDensity hGMeas hDensityMeas hDensityNonneg hGWeightedInt
    hFY_ne_zero



theorem thm_13_14_identity
    (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P]
    (fXY : ℝ × ℝ → ℝ)
    (hDensity : thm_13_14_jointDensityLaw P fXY)
    (hXMeas : Measurable (fun x : ℝ => x))
    (hDensityMeas : Measurable fXY)
    (hDensityNonneg : ∀ z : ℝ × ℝ, 0 ≤ fXY z)
    (hXWeightedInt : Integrable (fun z : ℝ × ℝ => fXY z * z.1) volume)
    (hFY_ne_zero : ∀ y : ℝ, thm_13_14_marginalDensity fXY y ≠ 0) :
    thm_13_14_isConditionalExpectationVersion P (fun x : ℝ => x)
      (thm_13_14_identityConditionalExpectationKernel fXY) :=
  thm_13_14 P fXY (fun x : ℝ => x)
    hDensity hXMeas hDensityMeas hDensityNonneg hXWeightedInt
    hFY_ne_zero
