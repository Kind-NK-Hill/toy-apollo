import Mathlib

open MeasureTheory
open scoped ENNReal

/-- A reusable bridge from a setwise density law to `Measure.withDensity`. -/
theorem phase2_measure_eq_withDensity_of_forall_measurable
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (ρ : α → ℝ≥0∞)
    (hρ : ∀ s : Set α, MeasurableSet s → μ s = ∫⁻ x in s, ρ x ∂ν) :
    μ = ν.withDensity ρ := by
  ext s hs
  rw [hρ s hs, withDensity_apply _ hs]

/-- Rewrite a Bochner set integral under a real density. The nonnegativity
assumption is explicit because `ENNReal.ofReal` discards negative values. -/
theorem phase2_setIntegral_withDensity_ofReal_eq
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (f φ : α → ℝ) (s : Set α)
    (hs : MeasurableSet s)
    (hμ : μ = ν.withDensity (fun x => ENNReal.ofReal (f x)))
    (hfMeas : AEMeasurable (fun x => ENNReal.ofReal (f x)) ν)
    (hfNonneg : ∀ᵐ x ∂ν, 0 ≤ f x) :
    (∫ x in s, φ x ∂μ) = ∫ x in s, f x * φ x ∂ν := by
  rw [hμ]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (hfMeas.mono_measure Measure.restrict_le_self) ?_ φ hs]
  · apply integral_congr_ae
    filter_upwards [ae_mono Measure.restrict_le_self hfNonneg] with x hx
    simp [ENNReal.toReal_ofReal hx, smul_eq_mul]
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

/-- Convert weighted integrability with respect to the base measure into
integrability with respect to the real-density measure. -/
theorem phase2_integrable_withDensity_ofReal_of_weighted
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (f φ : α → ℝ)
    (hμ : μ = ν.withDensity (fun x => ENNReal.ofReal (f x)))
    (hfMeas : AEMeasurable (fun x => ENNReal.ofReal (f x)) ν)
    (hfNonneg : ∀ᵐ x ∂ν, 0 ≤ f x)
    (hWeighted : Integrable (fun x => f x * φ x) ν) :
    Integrable φ μ := by
  rw [hμ]
  refine (integrable_withDensity_iff_integrable_smul₀' hfMeas ?_).2 ?_
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top
  · refine hWeighted.congr ?_
    filter_upwards [hfNonneg] with x hx
    simp [ENNReal.toReal_ofReal hx, smul_eq_mul]
