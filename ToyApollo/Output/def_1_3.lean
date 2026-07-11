/-
TASK ID: def_1_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Probability.CDF
import ToyApollo.Output.def_1_4
import ToyApollo.Output.def_1_3_kenneth_finite_support

open MeasureTheory ProbabilityTheory

noncomputable section

def CdfHasExpectationRS (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  ImproperRSIntegrable (fun x : ℝ => x) (cdf μ)

def CdfHasVarianceRS (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ) : Prop :=
  ImproperRSIntegrable (fun x : ℝ => (x - m) ^ 2) (cdf μ)

def cdfExpectationRS (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : CdfHasExpectationRS μ) : ℝ :=
  improperRSIntegral (fun x : ℝ => x) (cdf μ) h

theorem cdfExpectationRS_spec (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : CdfHasExpectationRS μ) :
    ImproperRSConvergesTo (fun x : ℝ => x) (cdf μ) (cdfExpectationRS μ h) := by
  exact improperRSIntegral_spec h

def cdfVarianceRS (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (h : CdfHasVarianceRS μ m) : ℝ :=
  improperRSIntegral (fun x : ℝ => (x - m) ^ 2) (cdf μ) h

theorem cdfVarianceRS_spec (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (h : CdfHasVarianceRS μ m) :
    ImproperRSConvergesTo (fun x : ℝ => (x - m) ^ 2) (cdf μ)
      (cdfVarianceRS μ m h) := by
  exact improperRSIntegral_spec h

theorem cdfExpectationRS_proof_irrel (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h₁ h₂ : CdfHasExpectationRS μ) :
    cdfExpectationRS μ h₁ = cdfExpectationRS μ h₂ := by
  exact ImproperRSConvergesTo.unique (cdfExpectationRS_spec μ h₁)
    (cdfExpectationRS_spec μ h₂)

theorem cdfVarianceRS_proof_irrel (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (h₁ h₂ : CdfHasVarianceRS μ m) :
    cdfVarianceRS μ m h₁ = cdfVarianceRS μ m h₂ := by
  exact ImproperRSConvergesTo.unique (cdfVarianceRS_spec μ m h₁)
    (cdfVarianceRS_spec μ m h₂)

structure CdfMomentData (μ : Measure ℝ) [IsProbabilityMeasure μ] where
  mean_integrable : CdfHasExpectationRS μ
  variance_integrable : CdfHasVarianceRS μ (cdfExpectationRS μ mean_integrable)

namespace CdfMomentData

def expectation {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (d : CdfMomentData μ) : ℝ :=
  cdfExpectationRS μ d.mean_integrable

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

def def_1_3 (μ : Measure ℝ) [IsProbabilityMeasure μ] := CdfMomentData μ

theorem def_1_3_cdf_measure (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (cdf μ).measure = μ :=
  measure_cdf μ
