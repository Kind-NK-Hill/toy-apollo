import Mathlib.Probability.CDF
import ToyApollo.Output.def_1_4
import ToyApollo.Output.def_1_3_kenneth_finite_support

open MeasureTheory ProbabilityTheory

noncomputable section

/-!
# Definition 1.3: expectation and variance from a probability CDF

The public integrator is `ProbabilityTheory.cdf μ` for an actual probability
measure `μ`. Whole-line values use the proof-carrying double-limit interface of
Definition 1.4. Kenneth's finite discrete, jump, density, and variance proofs
remain compiled support through the import above.
-/

/-- The textbook whole-line CDF expectation exists and is finite. -/
def CdfHasExpectationRS (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  ImproperRSIntegrable (fun x : ℝ => x) (cdf μ)

/-- The textbook whole-line CDF variance about `m` exists and is finite. -/
def CdfHasVarianceRS (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ) : Prop :=
  ImproperRSIntegrable (fun x : ℝ => (x - m) ^ 2) (cdf μ)

/-- Expectation chosen from the guarded improper Riemann--Stieltjes limit. -/
def cdfExpectationRS (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : CdfHasExpectationRS μ) : ℝ :=
  improperRSIntegral (fun x : ℝ => x) (cdf μ) h

/-- The chosen expectation satisfies the source double-limit specification. -/
theorem cdfExpectationRS_spec (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : CdfHasExpectationRS μ) :
    ImproperRSConvergesTo (fun x : ℝ => x) (cdf μ) (cdfExpectationRS μ h) := by
  exact improperRSIntegral_spec h

/-- Variance chosen from the guarded improper Riemann--Stieltjes limit. -/
def cdfVarianceRS (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (h : CdfHasVarianceRS μ m) : ℝ :=
  improperRSIntegral (fun x : ℝ => (x - m) ^ 2) (cdf μ) h

/-- The chosen variance satisfies the source double-limit specification. -/
theorem cdfVarianceRS_spec (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (h : CdfHasVarianceRS μ m) :
    ImproperRSConvergesTo (fun x : ℝ => (x - m) ^ 2) (cdf μ)
      (cdfVarianceRS μ m h) := by
  exact improperRSIntegral_spec h

/-- Proof irrelevance of the expectation witness. -/
theorem cdfExpectationRS_proof_irrel (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₁ h₂ : CdfHasExpectationRS μ) :
    cdfExpectationRS μ h₁ = cdfExpectationRS μ h₂ := by
  exact ImproperRSConvergesTo.unique (cdfExpectationRS_spec μ h₁)
    (cdfExpectationRS_spec μ h₂)

/-- Proof irrelevance of a variance witness about a fixed centre. -/
theorem cdfVarianceRS_proof_irrel (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (h₁ h₂ : CdfHasVarianceRS μ m) :
    cdfVarianceRS μ m h₁ = cdfVarianceRS μ m h₂ := by
  exact ImproperRSConvergesTo.unique (cdfVarianceRS_spec μ m h₁)
    (cdfVarianceRS_spec μ m h₂)

/-- Guarded expectation-and-variance data for Definition 1.3. -/
structure CdfMomentData (μ : Measure ℝ) [IsProbabilityMeasure μ] where
  mean_integrable : CdfHasExpectationRS μ
  variance_integrable : CdfHasVarianceRS μ (cdfExpectationRS μ mean_integrable)

namespace CdfMomentData

/-- The expectation carried by Definition 1.3 data. -/
def expectation {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (d : CdfMomentData μ) : ℝ :=
  cdfExpectationRS μ d.mean_integrable

/-- The variance carried by Definition 1.3 data. -/
def variance {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (d : CdfMomentData μ) : ℝ :=
  cdfVarianceRS μ d.expectation d.variance_integrable

theorem expectation_spec {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (d : CdfMomentData μ) :
    ImproperRSConvergesTo (fun x : ℝ => x) (cdf μ) d.expectation :=
  cdfExpectationRS_spec μ d.mean_integrable

theorem variance_spec {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (d : CdfMomentData μ) :
    ImproperRSConvergesTo (fun x : ℝ => (x - d.expectation) ^ 2) (cdf μ)
      d.variance :=
  cdfVarianceRS_spec μ d.expectation d.variance_integrable

end CdfMomentData

/-- Definition 1.3 for the genuine probability law `μ`. -/
def def_1_3 (μ : Measure ℝ) [IsProbabilityMeasure μ] := CdfMomentData μ

/-- The Stieltjes measure of the public CDF is the original probability law. -/
theorem def_1_3_cdf_measure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (cdf μ).measure = μ :=
  measure_cdf μ
