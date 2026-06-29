import Mathlib

/-
TASK ID: ex_7_4_1_variance_of_a_random_variable
TYPE: Example_Proof
SOURCE PLAN: 28_chap7_pushforward_change_of_variable
TASK CONTENT:
\textbf{Example 7.4.1 (Variance of a Random Variable)} \\
Let $X$ be a discrete random variable with pmf $P(X=i)=p_i$ for $i\ge 0$ and mean $m$. To evaluate the variance of $X$, we need not obtain the distribution of random variable $Y=(X-m)^2$, but rather compute it directly using the formula
\[
E[(X-m)^2] = \sum_i (i-m)^2 p_i.
\]
-/

-- WRITE FINAL LEAN CODE BELOW
open MeasureTheory

/-- The mean of a discrete random variable on `ℕ`, encoded by a probability mass function. -/
noncomputable def discretePmfMean (p : PMF ℕ) : ℝ :=
  ∫ i, (i : ℝ) ∂p.toMeasure

/-- The variance of a discrete random variable on `ℕ`, expressed directly from its pmf. -/
noncomputable def discretePmfVariance (p : PMF ℕ) : ℝ :=
  ∫ i, (((i : ℝ) - discretePmfMean p) ^ 2) ∂p.toMeasure

/-- For a discrete random variable, the variance can be computed directly from the pmf. -/
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

/-- Exported declaration for Example 7.4.1 (Variance of a Random Variable). -/
theorem ex_7_4_1_variance_of_a_random_variable (p : PMF ℕ)
    (h_var :
      Integrable (fun i : ℕ => (((i : ℝ) - discretePmfMean p) ^ 2)) p.toMeasure) :
    discretePmfVariance p = ∑' i : ℕ, (((i : ℝ) - discretePmfMean p) ^ 2) * (p i).toReal :=
  discretePmfVariance_eq_tsum p h_var
