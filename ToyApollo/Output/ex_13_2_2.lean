/-
TASK ID: ex_13_2_2
TYPE: Example_Proof
SOURCE PLAN: chapter13-sub-sigma-algebra
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_13_3

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

theorem ex_13_2_2_self_subSigma {Ω : Type*} [𝓕 : MeasurableSpace Ω] :
    IsSubSigmaField 𝓕 𝓕 := by
  intro A hA
  exact hA

theorem ex_13_2_2 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} (hXint : Integrable X P)
    (hXmeas : Measurable X) :
    @def_13_3 Ω 𝓕 P 𝓕 (@ex_13_2_2_self_subSigma Ω 𝓕) X X := by
  refine ⟨hXint, hXint, hXmeas, ?_⟩
  intro B hB
  rfl
