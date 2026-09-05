/-
TASK ID: prob_5_3
TYPE: Problem
SOURCE PLAN: 18_chap5_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




open MeasureTheory ProbabilityTheory

 
def IndepEvents {Ω : Type*} [MeasurableSpace Ω] (events : List (Set Ω)) (μ : Measure Ω) :
    Prop :=
  ∀ (S : Finset (Fin events.length)), 2 ≤ S.card →
    μ (⋂ i ∈ S, events.get i) = ∏ i ∈ S, μ (events.get i)

theorem prob_5_3 :
    ∃ (Ω : Type) (𝒜 : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (A₁ A₂ A₃ A₄ : Set Ω) (_ : MeasurableSet A₁) (_ : MeasurableSet A₂)
      (_ : MeasurableSet A₃) (_ : MeasurableSet A₄),
      P (A₁ ∩ A₂ ∩ A₃ ∩ A₄) = P A₁ * P A₂ * P A₃ * P A₄ ∧
        ¬ IndepEvents [A₁, A₂, A₃, A₄] P := by
  let P : MeasureTheory.Measure (Fin 2) :=
    MeasureTheory.Measure.dirac 0 + MeasureTheory.Measure.dirac 1 |>
      MeasureTheory.Measure.withDensity <| fun _ => 1 / 2
  refine' ⟨_, _, _, _, _⟩
  exact Fin 2
  exact inferInstance
  exact P
  · constructor
    norm_num [P]
    rw [← two_mul, ENNReal.mul_inv_cancel] <;> norm_num
  · refine' ⟨∅, {0}, {0}, {1}, _, _, _, _, _⟩ <;> norm_num [IndepEvents]
    refine' ⟨{⟨1, by decide⟩, ⟨3, by decide⟩}, _, _⟩ <;> norm_num [P]
