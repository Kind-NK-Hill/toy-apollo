/-
TASK ID: def_3_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_03.def_3_1
import Mathlib.MeasureTheory.Measure.MeasureSpace




open Set ENNReal Function



def IsSigmaFinite {Ω : Type*}
    {F₀ : FieldOfSets Ω}
    (μ : Premeasure F₀) : Prop :=
  ∃ (A : ℕ → Set Ω) (hA : ∀ i, A i ∈ F₀.carrier),
    (⋃ i, A i = univ) ∧ (∀ i, μ.μ₀ ⟨A i, hA i⟩ < ∞)
