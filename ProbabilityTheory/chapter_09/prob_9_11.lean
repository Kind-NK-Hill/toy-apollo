/-
TASK ID: prob_9_11
TYPE: Problem
SOURCE PLAN: chapter9-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_09.def_9_3
import ProbabilityTheory.chapter_09.thm_9_3




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable def squaredMagnitudeCharacteristicMeasure (μ : Measure ℝ) : Measure ℝ :=
  μ ∗ μ.map (fun x : ℝ => -x)

theorem squaredMagnitudeCharacteristicMeasure_isProbability
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (squaredMagnitudeCharacteristicMeasure μ) := by
  unfold squaredMagnitudeCharacteristicMeasure
  haveI : IsProbabilityMeasure (μ.map (fun x : ℝ => -x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  infer_instance

theorem charFun_reflectedMeasure_eq_star
    (μ : Measure ℝ) (t : ℝ) :
    charFun (μ.map (fun x : ℝ => -x)) t = star (charFun μ t) := by
  calc
    charFun (μ.map (fun x : ℝ => -x)) t = charFun μ ((-1 : ℝ) * t) := by
      simpa using (charFun_map_mul (μ := μ) (-1 : ℝ) t)
    _ = charFun μ (-t) := by simp
    _ = star (charFun μ t) := by
      simpa using (charFun_neg (μ := μ) t)

theorem squaredMagnitudeCharacteristicMeasure_charFun
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    charFun (squaredMagnitudeCharacteristicMeasure μ) t =
      charFun μ t * star (charFun μ t) := by
  rw [squaredMagnitudeCharacteristicMeasure]
  rw [characteristicFunction_convolution_product]
  rw [charFun_reflectedMeasure_eq_star]

theorem prob_9_11_law
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ t : ℝ, charFun ν t = charFun μ t * star (charFun μ t) := by
  refine ⟨squaredMagnitudeCharacteristicMeasure μ, ?_, ?_⟩
  · exact squaredMagnitudeCharacteristicMeasure_isProbability μ
  · intro t
    exact squaredMagnitudeCharacteristicMeasure_charFun μ t

theorem prob_9_11
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ t : ℝ,
        charFun ν t =
          characteristicFunction (P.map X) t *
            star (characteristicFunction (P.map X) t) := by
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  rcases prob_9_11_law (P.map X) with ⟨ν, hν, hν_charFun⟩
  refine ⟨ν, hν, ?_⟩
  intro t
  rw [hν_charFun t]
  rw [characteristicFunction_law_eq_charFun (μ := P) (X := X) hX t]
