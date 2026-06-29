import Mathlib
import ToyApollo.Output.def_9_1

/-
TASK ID: thm_9_1
TYPE: Theorem_Statement
SOURCE PLAN: chapter9-moments-mgf
TASK CONTENT:
By Theorem 7.12, we have the following formula for computing the moments of continuous-type random variables.

\begin{thmbox}{9.1}
Suppose $X$ is a random variable such that $\mathbb{E}[\lvert X\rvert^r] < \infty$. If the cdf $F_X(x)$ of $X$ is differentiable and the derivative equals $f_X(x)$, we can compute the $r$-th moment and the $r$-th central moment by the following formulas:
\[
\mathbb{E}[X^r] = \int_{-\infty}^{\infty} x^r f_X(x)\,dx,
\qquad
\mathbb{E}[(X-\mathbb{E}[X])^r] =
\int_{-\infty}^{\infty} (x-\mathbb{E}[X])^r f_X(x)\,dx.
\]
\end{thmbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

noncomputable abbrev densityMomentFormula (ρ : ℝ → NNReal) (r : ℕ) : ℝ :=
  ∫ x, x ^ r * (ρ x : ℝ)

noncomputable abbrev densityCentralMomentFormula
    (ρ : ℝ → NNReal) (mean : ℝ) (r : ℕ) : ℝ :=
  ∫ x, (x - mean) ^ r * (ρ x : ℝ)

theorem thm_9_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} (ρ : ℝ → NNReal) (r : ℕ)
    (hX : AEMeasurable X μ)
    (hρ : Measurable ρ)
    (hMap : Measure.map X μ = volume.withDensity fun x => ρ x) :
    rthMoment μ X r = densityMomentFormula ρ r ∧
      rthCentralMoment μ X r =
        densityCentralMomentFormula ρ (rthMoment μ X 1) r := by
  constructor
  · unfold rthMoment densityMomentFormula moment
    change (∫ x, X x ^ r ∂μ) = ∫ x, x ^ r * (ρ x : ℝ)
    calc
      ∫ x, X x ^ r ∂μ = ∫ y, y ^ r ∂Measure.map X μ := by
        exact
          (MeasureTheory.integral_map hX (f := fun y : ℝ => y ^ r) (by fun_prop)).symm
      _ = ∫ y, y ^ r ∂(volume.withDensity fun x => ρ x) := by
        rw [hMap]
      _ = ∫ x, x ^ r * (ρ x : ℝ) := by
        rw [integral_withDensity_eq_integral_smul hρ]
        simp [NNReal.smul_def, mul_comm]
  · unfold rthCentralMoment densityCentralMomentFormula centralMoment
    have hmean : rthMoment μ X 1 = ∫ x, X x ∂μ := by
      unfold rthMoment moment
      simp
    rw [hmean]
    change
      (∫ x, (X x - ∫ x, X x ∂μ) ^ r ∂μ) =
        ∫ x, (x - ∫ x, X x ∂μ) ^ r * (ρ x : ℝ)
    calc
      ∫ x, (X x - ∫ x, X x ∂μ) ^ r ∂μ =
          ∫ y, (y - ∫ x, X x ∂μ) ^ r ∂Measure.map X μ := by
        exact
          (MeasureTheory.integral_map hX
            (f := fun y : ℝ => (y - ∫ x, X x ∂μ) ^ r) (by fun_prop)).symm
      _ =
          ∫ y, (y - ∫ x, X x ∂μ) ^ r
            ∂(volume.withDensity fun x => ρ x) := by
        rw [hMap]
      _ = ∫ x, (x - ∫ x, X x ∂μ) ^ r * (ρ x : ℝ) := by
        rw [integral_withDensity_eq_integral_smul hρ]
        simp [NNReal.smul_def, mul_comm]
