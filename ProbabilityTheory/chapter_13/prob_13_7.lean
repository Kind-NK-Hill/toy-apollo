/-
TASK ID: prob_13_7
TYPE: Problem
SOURCE PLAN: chapter13-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_4




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

 
theorem prob_13_7_condVar_integral_eq_residual_square_given_sigma {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓖 : SigmaField Ω) (h𝓖 : 𝓖 ≤ 𝓕) {X : Ω → ℝ}
    (hX : MemLp X 2 P) :
    ∫ ω, Var[X; P | 𝓖] ω ∂P =
      ∫ ω, (X ω - P[X | 𝓖] ω) ^ 2 ∂P := by
  have hresInt : Integrable (fun ω => (X ω - P[X | 𝓖] ω) ^ 2) P := by
    simpa [Pi.sub_apply] using (hX.sub hX.condExp).integrable_sq
  simpa using
    (ProbabilityTheory.setIntegral_condVar
      (μ := P) (m := 𝓖) (X := X) (hm := h𝓖)
      (s := Set.univ) hresInt MeasurableSet.univ)

 
theorem prob_13_7_total_variance_given_sigma {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓖 : SigmaField Ω) (h𝓖 : 𝓖 ≤ 𝓕) {X : Ω → ℝ}
    (hX : MemLp X 2 P) :
    Var[X; P] =
      Var[P[X | 𝓖]; P] + ∫ ω, (X ω - P[X | 𝓖] ω) ^ 2 ∂P := by
  have htotal :
      ∫ ω, Var[X; P | 𝓖] ω ∂P + Var[P[X | 𝓖]; P] = Var[X; P] :=
    ProbabilityTheory.integral_condVar_add_variance_condExp
      (μ := P) (m := 𝓖) (X := X) h𝓖 hX
  have hres :
      ∫ ω, Var[X; P | 𝓖] ω ∂P =
        ∫ ω, (X ω - P[X | 𝓖] ω) ^ 2 ∂P :=
    @prob_13_7_condVar_integral_eq_residual_square_given_sigma Ω 𝓕 P inferInstance
      𝓖 h𝓖 X hX
  calc
    Var[X; P] = ∫ ω, Var[X; P | 𝓖] ω ∂P + Var[P[X | 𝓖]; P] := htotal.symm
    _ = Var[P[X | 𝓖]; P] + ∫ ω, (X ω - P[X | 𝓖] ω) ^ 2 ∂P := by
      rw [hres]
      ring

 
theorem prob_13_7_residual_square_given_sigma {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓖 : SigmaField Ω) (h𝓖 : 𝓖 ≤ 𝓕) {X : Ω → ℝ}
    (hX : MemLp X 2 P) :
    ∫ ω, (X ω - P[X | 𝓖] ω) ^ 2 ∂P =
      ∫ ω, (P[X ^ 2 | 𝓖] ω - P[X | 𝓖] ω ^ 2) ∂P := by
  have hleft :
      ∫ ω, Var[X; P | 𝓖] ω ∂P =
        ∫ ω, (X ω - P[X | 𝓖] ω) ^ 2 ∂P :=
    @prob_13_7_condVar_integral_eq_residual_square_given_sigma Ω 𝓕 P inferInstance
      𝓖 h𝓖 X hX
  have hright :
      ∫ ω, Var[X; P | 𝓖] ω ∂P =
        ∫ ω, (P[X ^ 2 | 𝓖] ω - P[X | 𝓖] ω ^ 2) ∂P := by
    exact integral_congr_ae
      (ProbabilityTheory.condVar_ae_eq_condExp_sq_sub_sq_condExp
        (μ := P) (m := 𝓖) (X := X) h𝓖 hX)
  exact hleft.symm.trans hright



theorem prob_13_7_total_variance_given_random_variable {Ω S : Type*}
    [𝓕 : MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (Y : Ω → S)
    (hY : Measurable Y) (hX : MemLp X 2 P) :
    Var[X; P] =
      Var[P[X | def_13_4_sigma Y]; P] +
        ∫ ω, (X ω - P[X | def_13_4_sigma Y] ω) ^ 2 ∂P := by
  have hσY : def_13_4_sigma Y ≤ 𝓕 := fun A hA => hY.comap_le A hA
  exact
    @prob_13_7_total_variance_given_sigma Ω 𝓕 P inferInstance
      (def_13_4_sigma Y) hσY X hX



theorem prob_13_7_residual_square_given_random_variable {Ω S : Type*}
    [𝓕 : MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    [IsProbabilityMeasure P] {X : Ω → ℝ} (Y : Ω → S)
    (hY : Measurable Y) (hX : MemLp X 2 P) :
    ∫ ω, (X ω - P[X | def_13_4_sigma Y] ω) ^ 2 ∂P =
      ∫ ω, (P[X ^ 2 | def_13_4_sigma Y] ω -
        P[X | def_13_4_sigma Y] ω ^ 2) ∂P := by
  have hσY : def_13_4_sigma Y ≤ 𝓕 := fun A hA => hY.comap_le A hA
  exact
    @prob_13_7_residual_square_given_sigma Ω 𝓕 P inferInstance
      (def_13_4_sigma Y) hσY X hX



theorem prob_13_7 {Ω S : Type*} [𝓕 : MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (Y : Ω → S)
    (hY : Measurable Y) (hX : MemLp X 2 P) :
    Var[X; P] =
        Var[P[X | def_13_4_sigma Y]; P] +
          ∫ ω, (X ω - P[X | def_13_4_sigma Y] ω) ^ 2 ∂P ∧
      ∫ ω, (X ω - P[X | def_13_4_sigma Y] ω) ^ 2 ∂P =
        ∫ ω, (P[X ^ 2 | def_13_4_sigma Y] ω -
          P[X | def_13_4_sigma Y] ω ^ 2) ∂P := by
  exact
    ⟨prob_13_7_total_variance_given_random_variable P Y hY hX,
      prob_13_7_residual_square_given_random_variable P Y hY hX⟩
