import Mathlib

/-
TASK ID: ex_8_3_1
TYPE: Example_Proof
SOURCE PLAN: 33_chap8_monge_kantorovich
TASK CONTENT:
\textbf{Example 8.3.1 (A Degenerate Example with Zero Transport Cost)} \\
Suppose random variables $\tilde{X}\sim N(0,\sigma^2)$ and $\tilde{Y}\sim N(0,\sigma^2)$ have the same distribution. Then the obvious transport map is the identity map, which actually does nothing. The optimal transport cost is 0.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

/-- Example 8.3.1: coupling a probability law with itself via the identity transport map produces
zero quadratic transport cost. This is the degenerate case behind the textbook Gaussian example. -/
theorem ex_8_3_1 (μ : Measure ℝ) :
    let h : ℝ → ℝ × ℝ := fun x => (x, x)
    Measure.map Prod.fst (Measure.map h μ) = μ ∧
      Measure.map Prod.snd (Measure.map h μ) = μ ∧
      (∫ z : ℝ × ℝ, (z.1 - z.2) ^ 2 ∂Measure.map h μ) = 0 := by
  dsimp
  have hh : Measurable (fun x : ℝ => (x, x)) := Measurable.prodMk measurable_id measurable_id
  have hcost :
      AEStronglyMeasurable (fun z : ℝ × ℝ => (z.1 - z.2) ^ 2)
        (Measure.map (fun x : ℝ => (x, x)) μ) := by
    fun_prop
  refine ⟨?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hh]
    change Measure.map id μ = μ
    exact Measure.map_id
  · rw [Measure.map_map measurable_snd hh]
    change Measure.map id μ = μ
    exact Measure.map_id
  · rw [integral_map hh.aemeasurable hcost]
    simp
