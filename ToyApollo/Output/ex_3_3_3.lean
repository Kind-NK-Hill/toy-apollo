import Mathlib

open MeasureTheory Set ENNReal ProbabilityTheory

/--
The measure induced by a nonnegative integrable density on `ℝ`.
-/
noncomputable def continuous_pdf_measure (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (f x)

/--
The density-built measure assigns `Iic x` the cumulative integral up to `x`.
-/
theorem continuous_pdf_measure_Iic (f : ℝ → ℝ) (hf_pos : ∀ x, 0 ≤ f x)
    (hf_int : Integrable f volume) (x : ℝ) :
    continuous_pdf_measure f (Iic x) = ENNReal.ofReal (∫ t in Iic x, f t) := by
  rw [continuous_pdf_measure, withDensity_apply _ measurableSet_Iic]
  have h_int : Integrable f (volume.restrict (Iic x)) := hf_int.restrict
  have h_nonneg : 0 ≤ᵐ[volume.restrict (Iic x)] f := Filter.Eventually.of_forall hf_pos
  simpa using (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg).symm

/--
The density-built measure assigns `(a, b)` the integral of the density over that interval.
-/
theorem continuous_pdf_measure_Ioo (f : ℝ → ℝ) (hf_pos : ∀ x, 0 ≤ f x)
    (hf_int : Integrable f volume) (a b : ℝ) :
    continuous_pdf_measure f (Ioo a b) = ENNReal.ofReal (∫ t in Ioo a b, f t) := by
  rw [continuous_pdf_measure, withDensity_apply _ measurableSet_Ioo]
  have h_int : Integrable f (volume.restrict (Ioo a b)) := hf_int.restrict
  have h_nonneg : 0 ≤ᵐ[volume.restrict (Ioo a b)] f := Filter.Eventually.of_forall hf_pos
  simpa using (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg).symm

/--
If the density integrates to `1`, the induced measure is a probability measure.
-/
theorem continuous_pdf_measure_univ (f : ℝ → ℝ) (hf_pos : ∀ x, 0 ≤ f x)
    (hf_int : Integrable f volume) (hf_norm : ∫ x, f x = 1) :
    continuous_pdf_measure f univ = 1 := by
  rw [continuous_pdf_measure, withDensity_apply _ MeasurableSet.univ]
  simpa [hf_norm] using
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int
      (Filter.Eventually.of_forall hf_pos)).symm

/--
The cumulative distribution function attached to `continuous_pdf_measure f`.
-/
noncomputable def continuous_pdf_cdf (f : ℝ → ℝ) : StieltjesFunction ℝ :=
  ProbabilityTheory.cdf (continuous_pdf_measure f)

/--
When `f` is a pdf, the cdf of the induced measure is exactly the cumulative integral
`x ↦ ∫_{(-∞, x]} f`.
-/
theorem continuous_pdf_cdf_eq_integral (f : ℝ → ℝ) (hf_pos : ∀ x, 0 ≤ f x)
    (hf_int : Integrable f volume) (hf_norm : ∫ x, f x = 1) (x : ℝ) :
    continuous_pdf_cdf f x = ∫ t in Iic x, f t := by
  let μ := continuous_pdf_measure f
  haveI : IsProbabilityMeasure μ := by
    constructor
    simpa [μ] using continuous_pdf_measure_univ f hf_pos hf_int hf_norm
  rw [continuous_pdf_cdf, ProbabilityTheory.cdf_eq_real, MeasureTheory.measureReal_def]
  rw [continuous_pdf_measure_Iic f hf_pos hf_int]
  refine ENNReal.toReal_ofReal ?_
  exact integral_nonneg fun _ => hf_pos _

/--
Example 3.3.3: a nonnegative integrable density with total mass `1` induces a continuous
distribution whose probability on `(a, b)` is `∫_a^b f(t) dt`.
-/
theorem ex_3_3_3 (f : ℝ → ℝ) (hf_pos : ∀ x, 0 ≤ f x)
    (hf_int : Integrable f volume) (hf_norm : ∫ x, f x = 1) (a b : ℝ) (hab : a < b) :
    (continuous_pdf_cdf f).measure (Ioo a b) = ENNReal.ofReal (∫ t in a..b, f t) := by
  let μ := continuous_pdf_measure f
  haveI : IsProbabilityMeasure μ := by
    constructor
    simpa [μ] using continuous_pdf_measure_univ f hf_pos hf_int hf_norm
  rw [continuous_pdf_cdf, ProbabilityTheory.measure_cdf]
  rw [continuous_pdf_measure_Ioo f hf_pos hf_int]
  rw [intervalIntegral.integral_of_le hab.le]
  congr 1
  exact (integral_Ioc_eq_integral_Ioo : ∫ t in Ioc a b, f t = ∫ t in Ioo a b, f t).symm
