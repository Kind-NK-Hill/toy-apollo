import ToyApollo.Output.def_1_3

open MeasureTheory ProbabilityTheory

noncomputable section

example (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  CdfHasExpectationRS μ

example (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : CdfHasExpectationRS μ) : ℝ :=
  cdfExpectationRS μ h

example (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : CdfHasExpectationRS μ) :
    ImproperRSConvergesTo (fun x : ℝ => x) (cdf μ) (cdfExpectationRS μ h) := by
  exact cdfExpectationRS_spec μ h

example (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (h : CdfHasVarianceRS μ m) : ℝ :=
  cdfVarianceRS μ m h

-- The repaired interface must not retain a public measure-equality evidence
-- structure. This assertion is checked by the separate forbidden-name scan.
