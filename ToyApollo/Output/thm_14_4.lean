/-
TASK ID: thm_14_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-weak-convergence
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_14_1
import ToyApollo.Output.thm_14_4_density_support

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set Metric
open scoped Topology ENNReal

noncomputable section

def thm_14_4_totalVariationConvergence
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ) : Prop :=
  Tendsto
    (fun n : ℕ => totalVariationDistance (Pseq n : Measure ℝ) (P : Measure ℝ))
    atTop (𝓝 (0 : ℝ))

theorem thm_14_4_of_boundedContinuousTestDifferenceBound
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV : thm_14_4_totalVariationConvergence Pseq P)
    (hBound : thm_14_4_boundedContinuousTestDifferenceBound Pseq P) :
    def_14_1 Pseq P := by
  intro h
  let L : ℝ := ∫ x, h x ∂(P : Measure ℝ)
  have hRhs :
      Tendsto
        (fun n : ℕ =>
          (2 * ‖h‖) * totalVariationDistance (Pseq n : Measure ℝ) (P : Measure ℝ))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using hTV.const_mul (2 * ‖h‖)
  have hAbs :
      Tendsto
        (fun n : ℕ => |(∫ x, h x ∂(Pseq n : Measure ℝ)) - L|)
        atTop (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun n => abs_nonneg _) ?_ hRhs
    intro n
    simpa [L] using hBound n h
  have hSub :
      Tendsto
        (fun n : ℕ => (∫ x, h x ∂(Pseq n : Measure ℝ)) - L)
        atTop (𝓝 (0 : ℝ)) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Real.norm_eq_abs] using hAbs
  have hConst : Tendsto (fun _n : ℕ => L) atTop (𝓝 L) :=
    tendsto_const_nhds
  have hAdd :
      Tendsto
        (fun n : ℕ => ((∫ x, h x ∂(Pseq n : Measure ℝ)) - L) + L)
        atTop (𝓝 (0 + L)) :=
    hSub.add hConst
  simpa [L, sub_add_cancel] using hAdd

theorem thm_14_4
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (hTV : thm_14_4_totalVariationConvergence Pseq P) :
    def_14_1 Pseq P := by
  exact thm_14_4_of_boundedContinuousTestDifferenceBound Pseq P hTV
    (thm_14_4_boundedContinuousTestDifferenceBound_from_rn Pseq P)

structure thm_14_4_ConverseFailureWitness where
  discrete_laws : ℕ → ProbabilityMeasure ℝ
  continuous_law : ProbabilityMeasure ℝ
  weak_convergence : def_14_1 discrete_laws continuous_law
  total_variation_distance_one :
    ∀ n : ℕ,
      totalVariationDistance (discrete_laws n : Measure ℝ) (continuous_law : Measure ℝ) = 1

theorem thm_14_4_converseFailure_not_totalVariation
    (W : thm_14_4_ConverseFailureWitness) :
    ¬ thm_14_4_totalVariationConvergence W.discrete_laws W.continuous_law := by
  intro hTV
  have hconst :
      Tendsto
        (fun n : ℕ =>
          totalVariationDistance
            (W.discrete_laws n : Measure ℝ) (W.continuous_law : Measure ℝ))
        atTop (𝓝 (1 : ℝ)) := by
    simp [W.total_variation_distance_one]
  have huniq := tendsto_nhds_unique hTV hconst
  exact one_ne_zero huniq.symm

theorem thm_14_4_converseFailure_note
    (W : thm_14_4_ConverseFailureWitness) :
    def_14_1 W.discrete_laws W.continuous_law ∧
      ¬ thm_14_4_totalVariationConvergence W.discrete_laws W.continuous_law :=
  ⟨W.weak_convergence, thm_14_4_converseFailure_not_totalVariation W⟩
