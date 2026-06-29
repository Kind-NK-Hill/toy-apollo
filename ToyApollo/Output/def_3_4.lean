import Mathlib.Probability.CDF

open MeasureTheory Set ProbabilityTheory

/-- Let (ℝ, 𝓑(ℝ), P) be a probability space. The distribution function induced by P
is defined as F(x) = P((-∞, x]) for x ∈ ℝ. -/
noncomputable def distributionFunction (P : Measure ℝ) [IsProbabilityMeasure P] (x : ℝ) : ℝ :=
  (P (Iic x)).toReal