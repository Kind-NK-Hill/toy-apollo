/-
TASK ID: prob_2_5
TYPE: Problem
SOURCE PLAN: 45_chap2_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set Filter Topology

theorem prob_2_5 :
    ∃ (Ω : Type) (_ : Countable Ω) (m : MeasurableSpace Ω) (μ : Measure Ω)
      (A : ℕ → Set Ω),
      μ = Measure.count ∧
        (∀ n, MeasurableSet (A n)) ∧ (∀ n, A (n + 1) ⊆ A n) ∧
        (⋂ n, A n) = ∅ ∧ ¬ Tendsto (fun n => μ (A n)) atTop (𝓝 0) := by
  refine ⟨ℕ, inferInstance, ⊤, Measure.count, fun n => Set.Ici n, rfl, ?_, ?_, ?_, ?_⟩
  · intro n
    exact measurableSet_Ici
  · intro n x hx
    simp [Set.mem_Ici] at *
    omega
  · ext x
    simp only [Set.mem_iInter, Set.mem_Ici, Set.mem_empty_iff_false, iff_false, not_forall]
    exact ⟨x + 1, by omega⟩
  · rw [ENNReal.tendsto_nhds_zero]
    norm_num
    refine ⟨1, by norm_num, fun n => ⟨n, le_rfl, ?_⟩⟩
    erw [Measure.count_apply_infinite]
    · norm_num
    · exact Set.Ici_infinite n
