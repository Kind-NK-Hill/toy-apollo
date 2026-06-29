/-
TASK ID: thm_8_1
TYPE: Theorem_with_Proof
SOURCE PLAN: 31_chap8_coupling
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.ex_3_3_4

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem thm_8_1
    {α β Ω : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace Ω]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [MeasurableSingletonClass Ω]
    {μ : Measure Ω} {P : Measure α} {Q : Measure β}
    {X : Ω → α} {Y : Ω → β}
    (hX : Measurable X) (hY : Measurable Y)
    (hPX : Measure.map X μ = P) (hQY : Measure.map Y μ = Q) :
    ∃! h : Ω → α × β,
      Measurable h ∧
      Prod.fst ∘ h = X ∧
      Prod.snd ∘ h = Y ∧
      Measure.map Prod.fst (Measure.map h μ) = P ∧
      Measure.map Prod.snd (Measure.map h μ) = Q := by
  let h : Ω → α × β := fun ω => (X ω, Y ω)
  have hh : Measurable h := Measurable.prodMk hX hY
  refine ⟨h, ?_, ?_⟩
  · refine ⟨hh, rfl, rfl, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hh]
      simpa [h, Function.comp]
        using hPX
    · rw [Measure.map_map measurable_snd hh]
      simpa [h, Function.comp]
        using hQY
  · intro h' hh'
    rcases hh' with ⟨hh'm, hh'fst, hh'snd, _, _⟩
    funext ω
    apply Prod.ext
    · simpa [Function.comp] using congrFun hh'fst ω
    · simpa [Function.comp] using congrFun hh'snd ω
