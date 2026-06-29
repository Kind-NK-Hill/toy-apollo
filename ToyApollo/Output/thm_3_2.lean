/-
TASK ID: thm_3_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_3_4
import Mathlib.Probability.CDF

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology

theorem distributionFunction_properties (P : Measure ℝ) [IsProbabilityMeasure P] :
    Monotone (distributionFunction P) ∧
    (∀ x, ContinuousWithinAt (distributionFunction P) (Ici x) x) ∧
    Tendsto (distributionFunction P) atTop (𝓝 1) ∧
    Tendsto (distributionFunction P) atBot (𝓝 0) := by
  -- We prove that our distributionFunction is equivalent to the standard Mathlib cdf.
  have h_eq : distributionFunction P = cdf P := by
    ext x
    rw [distributionFunction, ← ofReal_cdf P x]
    -- Since cdf P x is the underlying function of a StieltjesFunction, it is always finite.
    -- cdf_nonneg ensures the value is non-negative, allowing ENNReal.toReal_ofReal to simplify.
    exact ENNReal.toReal_ofReal (cdf_nonneg P x)

  -- Use the properties provided by the cdf API.
  rw [h_eq]
  refine ⟨(cdf P).mono, (cdf P).right_continuous, tendsto_cdf_atTop P, tendsto_cdf_atBot P⟩
