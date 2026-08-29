/-
TASK ID: thm_5_7
TYPE: Theorem_Statement
SOURCE PLAN: 15_chap5_independence_multiple_rv
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_5_5

-- WRITE FINAL LEAN CODE BELOW

theorem thm_5_7 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ} (A : Fin n → Set Ω)
    (hMeas : ∀ i, MeasurableSet (A i)) :
    def_5_5 μ A ↔
      ProbabilityTheory.iIndep (fun i : Fin n => MeasurableSpace.generateFrom {A i}) μ := by
  exact
    (def_5_5_iff_iIndepSet μ A hMeas).trans
      (ProbabilityTheory.iIndepSet_iff_iIndep A μ)
