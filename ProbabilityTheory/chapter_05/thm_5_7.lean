/-
TASK ID: thm_5_7
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import ProbabilityTheory.chapter_05.def_5_5to10



theorem thm_5_7 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) {n : ℕ}
    (A : Fin n → Set Ω) :
    def_5_5 μ A ↔ ProbabilityTheory.iIndep (fun k : Fin n => MeasurableSpace.generateFrom {A k}) μ := by
  simpa [def_5_5] using (ProbabilityTheory.iIndepSet_iff_iIndep (s := A) (μ := μ))
