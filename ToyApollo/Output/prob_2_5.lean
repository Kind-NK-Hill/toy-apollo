import Mathlib

/-
TASK ID: prob_2_5
TYPE: Problem
SOURCE PLAN: 45_chap2_problems
TASK CONTENT:
\textbf{2.5.} Consider the counting measure $\mu$ on a countable sample space $\Omega$. Construct a sequence of decreasing sets $A_1\supseteq A_2\supseteq A_3\supseteq \cdots$ such that $\cap_{i=1}^{\infty} A_i=\emptyset$, but $\lim_{i\to\infty} \mu(A_i)\neq 0$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set Filter Topology

/-
Problem 2.5: Construct decreasing sets on a countable space with counting measure
whose intersection is empty but whose measures do not tend to 0.
-/
theorem prob_2_5 :
    ∃ (Ω : Type) (_ : Countable Ω) (m : MeasurableSpace Ω) (μ : Measure Ω)
      (A : ℕ → Set Ω),
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, A (n + 1) ⊆ A n) ∧
        (⋂ n, A n) = ∅ ∧ ¬ Tendsto (fun n => μ (A n)) atTop (𝓝 0) := by
  refine ⟨ℕ, inferInstance, ⊤, Measure.count, fun n => Set.Ici n, ?_, ?_, ?_, ?_⟩
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
