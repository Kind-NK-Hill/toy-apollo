/-
TASK ID: ex_7_4_1_variance_of_a_random_variable
TYPE: Example_Proof
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW
open MeasureTheory

noncomputable def discretePmfMean (p : PMF ℕ) : ℝ :=
  ∫ i, (i : ℝ) ∂p.toMeasure

noncomputable def discretePmfVariance (p : PMF ℕ) : ℝ :=
  ∫ i, (((i : ℝ) - discretePmfMean p) ^ 2) ∂p.toMeasure

theorem discretePmfVariance_eq_tsum (p : PMF ℕ)
    (h_var :
      Integrable (fun i : ℕ => (((i : ℝ) - discretePmfMean p) ^ 2)) p.toMeasure) :
    discretePmfVariance p = ∑' i : ℕ, (((i : ℝ) - discretePmfMean p) ^ 2) * (p i).toReal := by
  rw [discretePmfVariance]
  calc
    ∫ i, (((i : ℝ) - discretePmfMean p) ^ 2) ∂p.toMeasure
      = ∑' i : ℕ, (p i).toReal • (((i : ℝ) - discretePmfMean p) ^ 2) := by
          simpa using
            (PMF.integral_eq_tsum p (fun i : ℕ => (((i : ℝ) - discretePmfMean p) ^ 2)) h_var)
    _ = ∑' i : ℕ, (((i : ℝ) - discretePmfMean p) ^ 2) * (p i).toReal := by
          refine tsum_congr ?_
          intro i
          rw [smul_eq_mul, mul_comm]

theorem ex_7_4_1_variance_of_a_random_variable (p : PMF ℕ)
    (h_var :
      Integrable (fun i : ℕ => (((i : ℝ) - discretePmfMean p) ^ 2)) p.toMeasure) :
    discretePmfVariance p = ∑' i : ℕ, (((i : ℝ) - discretePmfMean p) ^ 2) * (p i).toReal :=
  discretePmfVariance_eq_tsum p h_var
