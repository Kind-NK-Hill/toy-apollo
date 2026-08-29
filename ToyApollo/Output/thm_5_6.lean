/-
TASK ID: thm_5_6
TYPE: Theorem_with_Proof
SOURCE PLAN: 15_chap5_independence_multiple_rv
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_5_5

-- WRITE FINAL LEAN CODE BELOW

theorem thm_5_6 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ} (A : Fin n → Set Ω)
    (hMeas : ∀ i, MeasurableSet (A i)) (i : Fin n) (hA : def_5_5 μ A) :
    def_5_5 μ (Function.update A i ((A i)ᶜ)) := by
  let B : Fin n → Set Ω := Function.update A i ((A i)ᶜ)
  have hBMeas : ∀ j, MeasurableSet (B j) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [B] using (hMeas i).compl
    · simpa [B, hji] using hMeas j
  have hIndepSet : ProbabilityTheory.iIndepSet A μ :=
    (def_5_5_iff_iIndepSet μ A hMeas).1 hA
  have hIndep :
      ProbabilityTheory.iIndep (fun j : Fin n => MeasurableSpace.generateFrom {A j}) μ :=
    (ProbabilityTheory.iIndepSet_iff_iIndep A μ).1 hIndepSet
  have hle :
      ∀ j : Fin n, MeasurableSpace.generateFrom {B j} ≤ MeasurableSpace.generateFrom {A j} := by
    intro j
    apply MeasurableSpace.generateFrom_le
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst s
    by_cases hji : j = i
    · subst j
      simpa [B] using
        (MeasurableSpace.measurableSet_generateFrom
          (show A i ∈ ({A i} : Set (Set Ω)) by simp)).compl
    · simpa [B, hji] using
        (MeasurableSpace.measurableSet_generateFrom
          (show A j ∈ ({A j} : Set (Set Ω)) by simp))
  apply (def_5_5_iff_iIndepSet μ B hBMeas).2
  exact
    (ProbabilityTheory.iIndepSet_iff_iIndep B μ).2
      (ProbabilityTheory.iIndep_of_iIndep_of_le hIndep hle)
