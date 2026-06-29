import Mathlib

/-
TASK ID: prob_5_5
TYPE: Problem
SOURCE PLAN: 18_chap5_problems
TASK CONTENT:
\item Show that the independence of two random variables depends on the choice of probability measure. Give an example of measurable space $(\Omega, \mathcal{F})$, two random variables $X(\omega)$ and $Y(\omega)$, and two probability measures $P$ and $Q$, such that $X$ and $Y$ are independent with probability measure $P$ but are dependent with probability measure $Q$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory MeasurableSpace

theorem prob_5_5 :
    ∃ (Ω : Type) (𝒜 : MeasurableSpace Ω) (P Q : @Measure Ω 𝒜)
      (_ : @IsProbabilityMeasure Ω 𝒜 P) (_ : @IsProbabilityMeasure Ω 𝒜 Q)
      (X Y : Ω → ℝ) (_ : @Measurable Ω ℝ 𝒜 _ X) (_ : @Measurable Ω ℝ 𝒜 _ Y),
      @IndepFun Ω ℝ ℝ 𝒜 _ _ X Y P ∧ ¬ @IndepFun Ω ℝ ℝ 𝒜 _ _ X Y Q := by
  use Fin 2 × Fin 2
  use inferInstance
  refine' ⟨MeasureTheory.Measure.dirac (0, 0),
    MeasureTheory.Measure.dirac (0, 0) + MeasureTheory.Measure.dirac (1, 1) |>
      MeasureTheory.Measure.withDensity <| fun _ => 1 / 2, _, _, _⟩ <;> norm_num
  · infer_instance
  · constructor
    norm_num
    rw [← two_mul, ENNReal.mul_inv_cancel] <;> norm_num
  · refine' ⟨fun x => x.1, fun x => x.2, _, _, _, _⟩ <;>
      norm_num [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
    · intro s t hs ht
      by_cases hs0 : 0 ∈ s <;> by_cases ht0 : 0 ∈ t <;> simp +decide [hs0, ht0]
    · exact measurable_from_prod_countable_right' (fun x ⦃t⦄ a => trivial) fun x x' y => congrFun rfl
    · exact Measurable.of_discrete
    · refine' ⟨{0}, _, {1}, _, _⟩ <;> norm_num [Set.indicator]
