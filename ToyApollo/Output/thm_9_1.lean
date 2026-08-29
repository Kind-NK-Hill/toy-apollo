/-
TASK ID: thm_9_1
TYPE: Theorem_Statement
SOURCE PLAN: chapter9-moments-mgf
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_9_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

noncomputable abbrev densityMomentFormula (ρ : ℝ → NNReal) (r : ℕ) : ℝ :=
  ∫ x, x ^ r * (ρ x : ℝ)

noncomputable abbrev densityCentralMomentFormula
    (ρ : ℝ → NNReal) (mean : ℝ) (r : ℕ) : ℝ :=
  ∫ x, (x - mean) ^ r * (ρ x : ℝ)

theorem thm_9_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (ρ : ℝ → NNReal) (r : PositiveOrder)
    (hX : FiniteAbsMoment μ X r.1)
    (hρ : Measurable ρ)
    (hMap : Measure.map X μ = volume.withDensity fun x => ρ x) :
    rthMoment μ X r hX = densityMomentFormula ρ r.1 ∧
      rthCentralMoment μ X r hX =
        densityCentralMomentFormula ρ
          (rthMoment μ X positiveOrderOne (hX.mono r.property)) r.1 := by
  constructor
  · unfold rthMoment generalMoment densityMomentFormula moment
    change (∫ x, X x ^ r.1 ∂μ) = ∫ x, x ^ r.1 * (ρ x : ℝ)
    calc
      ∫ x, X x ^ r.1 ∂μ = ∫ y, y ^ r.1 ∂Measure.map X μ := by
        exact
          (MeasureTheory.integral_map hX.1.aemeasurable
            (f := fun y : ℝ => y ^ r.1) (by fun_prop)).symm
      _ = ∫ y, y ^ r.1 ∂(volume.withDensity fun x => ρ x) := by
        rw [hMap]
      _ = ∫ x, x ^ r.1 * (ρ x : ℝ) := by
        rw [integral_withDensity_eq_integral_smul hρ]
        simp [NNReal.smul_def, mul_comm]
  · unfold rthCentralMoment densityCentralMomentFormula centralMoment
    have hmean :
        rthMoment μ X positiveOrderOne (hX.mono r.property) =
          ∫ x, X x ∂μ := by
      unfold rthMoment generalMoment positiveOrderOne moment
      simp
    rw [hmean]
    change
      (∫ x, (X x - ∫ x, X x ∂μ) ^ r.1 ∂μ) =
        ∫ x, (x - ∫ x, X x ∂μ) ^ r.1 * (ρ x : ℝ)
    calc
      ∫ x, (X x - ∫ x, X x ∂μ) ^ r.1 ∂μ =
          ∫ y, (y - ∫ x, X x ∂μ) ^ r.1 ∂Measure.map X μ := by
        exact
          (MeasureTheory.integral_map hX.1.aemeasurable
            (f := fun y : ℝ => (y - ∫ x, X x ∂μ) ^ r.1) (by fun_prop)).symm
      _ =
          ∫ y, (y - ∫ x, X x ∂μ) ^ r.1
            ∂(volume.withDensity fun x => ρ x) := by
        rw [hMap]
      _ = ∫ x, (x - ∫ x, X x ∂μ) ^ r.1 * (ρ x : ℝ) := by
        rw [integral_withDensity_eq_integral_smul hρ]
        simp [NNReal.smul_def, mul_comm]
