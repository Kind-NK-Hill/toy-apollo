import Mathlib

open MeasureTheory intervalIntegral
open scoped Real

noncomputable section

/-- The discrete cdf contribution in Example 1.3.2, coming from the two atoms at `± 1.5`. -/
def mixedDiscretePart (p : ℝ) : ℝ → ℝ :=
  fun x =>
    p * Set.indicator (Set.Ici (-3 / 2 : ℝ)) (fun _ => (1 : ℝ)) x +
      p * Set.indicator (Set.Ici (3 / 2 : ℝ)) (fun _ => (1 : ℝ)) x

/-- The standard normal density kernel used in the continuous part. -/
def standardNormalKernel (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

/-- The continuous cdf contribution in Example 1.3.2. -/
def mixedContinuousPart (p : ℝ) : ℝ → ℝ :=
  fun x =>
    if x < (-3 / 2 : ℝ) then 0
    else if x < (3 / 2 : ℝ) then
      (1 - 2 * p) * ∫ t in (-3 / 2 : ℝ)..x, standardNormalKernel t
    else 1 - 2 * p

/-- The discrete expectation contribution from the two point masses. -/
def mixedDiscreteExpectation (p : ℝ) : ℝ :=
  (-3 / 2 : ℝ) * p + (3 / 2 : ℝ) * p

/-- The continuous expectation contribution from the truncated symmetric Gaussian part. -/
def mixedContinuousExpectation (p : ℝ) : ℝ :=
  ∫ y in (-(3 / 2 : ℝ))..(3 / 2 : ℝ), y * ((1 - 2 * p) * standardNormalKernel y)

/-- Exported concrete decomposition for Example 1.3.2. -/
structure MixedTypeExpectationData where
  discretePart : ℝ → ℝ
  continuousPart : ℝ → ℝ
  discreteContribution : ℝ
  continuousContribution : ℝ

/-- Exported declaration for Example 1.3.2. -/
def ex_1_3_2 (p : ℝ) : MixedTypeExpectationData where
  discretePart := mixedDiscretePart p
  continuousPart := mixedContinuousPart p
  discreteContribution := mixedDiscreteExpectation p
  continuousContribution := mixedContinuousExpectation p

/-- The standard normal kernel is even. -/
theorem standardNormalKernel_even (x : ℝ) :
    standardNormalKernel (-x) = standardNormalKernel x := by
  simp [standardNormalKernel, neg_sq]

/-- The integrand for the continuous contribution is odd. -/
theorem mixedContinuousIntegrand_odd (p x : ℝ) :
    (-x) * ((1 - 2 * p) * standardNormalKernel (-x)) =
      -(x * ((1 - 2 * p) * standardNormalKernel x)) := by
  rw [standardNormalKernel_even]
  ring

/-- The two atomic contributions cancel by symmetry. -/
theorem mixedDiscreteExpectation_eq_zero (p : ℝ) :
    mixedDiscreteExpectation p = 0 := by
  unfold mixedDiscreteExpectation
  ring

/-- The continuous contribution vanishes because the density term is even and the factor `y` is odd. -/
theorem mixedContinuousExpectation_eq_zero (p : ℝ) :
    mixedContinuousExpectation p = 0 := by
  let c : ℝ := 3 / 2
  let g : ℝ → ℝ := fun y => y * ((1 - 2 * p) * standardNormalKernel y)
  have hcomp :
      ∫ x in (-c : ℝ)..c, g (-x) = mixedContinuousExpectation p := by
    simpa [c, g, mixedContinuousExpectation] using
      (intervalIntegral.integral_comp_neg (f := g) (a := (-c : ℝ)) (b := c))
  have hodd :
      ∫ x in (-c : ℝ)..c, g (-x) = -mixedContinuousExpectation p := by
    calc
      ∫ x in (-c : ℝ)..c, g (-x)
          = ∫ x in (-c : ℝ)..c, -g x := by
              congr with x
              have hx := mixedContinuousIntegrand_odd p x
              simpa [g] using hx
      _ = -∫ x in (-c : ℝ)..c, g x := by rw [intervalIntegral.integral_neg]
      _ = -mixedContinuousExpectation p := by
            simp [c, g, mixedContinuousExpectation]
  have hself : mixedContinuousExpectation p = -mixedContinuousExpectation p := by
    calc
      mixedContinuousExpectation p = ∫ x in (-c : ℝ)..c, g (-x) := by simpa using hcomp.symm
      _ = -mixedContinuousExpectation p := hodd
  linarith

/-- The source decomposition `E[Y] = ∫ y dα₁ + ∫ y dα₂` is recorded by the two concrete contributions. -/
theorem ex_1_3_2_expectation_split (p : ℝ) :
    (ex_1_3_2 p).discreteContribution + (ex_1_3_2 p).continuousContribution = 0 := by
  change mixedDiscreteExpectation p + mixedContinuousExpectation p = 0
  rw [mixedDiscreteExpectation_eq_zero, mixedContinuousExpectation_eq_zero]
  ring

/-- The mixed-type example has mean zero by symmetry. -/
theorem ex_1_3_2_mean_zero (p : ℝ) :
    (ex_1_3_2 p).discreteContribution + (ex_1_3_2 p).continuousContribution = 0 := by
  exact ex_1_3_2_expectation_split p
