import Mathlib
import ToyApollo.Output.thm_14_1
import ToyApollo.Output.prob_14_3

/-
TASK ID: prob_14_4
TYPE: Problem
SOURCE PLAN: chapter14-problems
TASK CONTENT:
\textbf{14.4.} For n = 1, 2, 3,... ,l e t Xn be a Gaussian random variable with distribution

N( 0,1/n)Show that Xn converges in distribution, and find the limit distribution.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

/-- The characteristic function of `N(0, 1/(n+1))`.

As in the neighboring problem, Lean uses `ℕ` indexing, so textbook `n ≥ 1`
corresponds to variance `(n+1)⁻¹`. -/
def prob_14_4_gaussianCharacteristic (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((-((((n : ℝ) + 1)⁻¹) * t ^ 2 / 2)) : ℝ) : ℂ)

/-- The limiting distribution is the point mass at zero. -/
def prob_14_4_limitDistribution : ProbabilityMeasure ℝ :=
  diracProba (0 : ℝ)

/-- The characteristic function of the limiting point mass is constantly `1`. -/
def prob_14_4_limitCharacteristic (_t : ℝ) : ℂ :=
  1

/-- The concrete setup for the shrinking centered Gaussian sequence. -/
structure prob_14_4_ShrinkingGaussianSetup where
  gaussianLaws : ℕ → ProbabilityMeasure ℝ
  gaussian_law :
    ∀ n : ℕ,
      prob_14_3_isCenteredGaussianLaw
        (gaussianLaws n) (((n : ℝ) + 1)⁻¹)

/-- The setup gives the displayed characteristic function
`exp(-t^2/(2(n+1)))`. -/
theorem prob_14_4_gaussian_characteristic
    (S : prob_14_4_ShrinkingGaussianSetup) (n : ℕ) (t : ℝ) :
    thm_14_1_characteristicFunction (S.gaussianLaws n) t =
      prob_14_4_gaussianCharacteristic n t := by
  simpa [prob_14_4_gaussianCharacteristic] using S.gaussian_law n t

/-- The point mass at zero has characteristic function `1`. -/
theorem prob_14_4_dirac_zero_characteristic (t : ℝ) :
    thm_14_1_characteristicFunction prob_14_4_limitDistribution t =
      prob_14_4_limitCharacteristic t := by
  rw [prob_14_4_limitDistribution, prob_14_4_limitCharacteristic,
    thm_14_1_characteristicFunction]
  change charFun (Measure.dirac (0 : ℝ)) t = (1 : ℂ)
  simp

/-- The shrinking Gaussian characteristic functions converge pointwise to the
constant characteristic function of the point mass at zero. -/
theorem prob_14_4_gaussian_characteristic_limit
    (S : prob_14_4_ShrinkingGaussianSetup) :
    thm_14_1_pointwiseCharFunConvergence
      S.gaussianLaws prob_14_4_limitCharacteristic := by
  intro t
  have hbase :
      Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hreal :
      Tendsto (fun n : ℕ => -((((n : ℝ) + 1)⁻¹) * t ^ 2 / 2))
        atTop (𝓝 (0 : ℝ)) := by
    have hscaled :
        Tendsto
          (fun n : ℕ => (-(t ^ 2 / 2)) * (((n : ℝ) + 1)⁻¹))
          atTop (𝓝 ((-(t ^ 2 / 2)) * 0)) := by
      exact tendsto_const_nhds.mul hbase
    convert hscaled using 1
    · ext n
      ring_nf
    · ring_nf
  have hcomplex :
      Tendsto
        (fun n : ℕ =>
          ((-((((n : ℝ) + 1)⁻¹) * t ^ 2 / 2) : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) := by
    change
      Tendsto
        (fun n : ℕ =>
          Complex.ofReal (-((((n : ℝ) + 1)⁻¹) * t ^ 2 / 2)))
        atTop (𝓝 (Complex.ofReal 0))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hexp := hcomplex.cexp
  rw [show prob_14_4_limitCharacteristic t = (1 : ℂ) by rfl]
  convert hexp using 1
  · ext n
    rw [prob_14_4_gaussian_characteristic S n t]
    rfl
  · simp

/-- The shrinking Gaussian laws converge weakly to the point mass at zero. -/
theorem prob_14_4_converges_to_dirac_zero
    (S : prob_14_4_ShrinkingGaussianSetup) :
    Tendsto S.gaussianLaws atTop (𝓝 prob_14_4_limitDistribution) := by
  exact
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun
      (μ := S.gaussianLaws) (μ₀ := prob_14_4_limitDistribution)).2
      (fun t => by
        have h := prob_14_4_gaussian_characteristic_limit S t
        rw [← prob_14_4_dirac_zero_characteristic t] at h
        simpa [thm_14_1_characteristicFunction] using h)

/-- In the language of Theorem 14.1, the limit characteristic function is the
characteristic function of the point mass at zero. -/
theorem prob_14_4_limit_is_dirac_zero_characteristic :
    thm_14_1_limitIsCharacteristic prob_14_4_limitCharacteristic := by
  refine ⟨prob_14_4_limitDistribution, ?_⟩
  intro t
  exact (prob_14_4_dirac_zero_characteristic t).symm

/-- Problem 14.4: `N(0,1/n)` converges in distribution to the degenerate
distribution at zero. -/
theorem prob_14_4
    (S : prob_14_4_ShrinkingGaussianSetup) :
    Tendsto S.gaussianLaws atTop (𝓝 prob_14_4_limitDistribution) ∧
      thm_14_1_weakLimit S.gaussianLaws ∧
        thm_14_1_limitIsCharacteristic prob_14_4_limitCharacteristic := by
  have hconv := prob_14_4_converges_to_dirac_zero S
  exact ⟨hconv, ⟨prob_14_4_limitDistribution, hconv⟩,
    prob_14_4_limit_is_dirac_zero_characteristic⟩
