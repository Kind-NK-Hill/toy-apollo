/-
TASK ID: prob_7_5
TYPE: Problem
SOURCE PLAN: 30_chap7_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter Topology

theorem prob_7_5 {Ω : Type} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (X : ℕ → Ω → ℝ) (X_lim : Ω → ℝ) (K : ℝ)
    (h_meas : ∀ n, Measurable (X n)) (h_nonneg : ∀ n, ∀ ω, 0 ≤ X n ω)
    (h_lintegral_bound : ∀ n, ∫⁻ ω, ENNReal.ofReal (X n ω) ∂μ < ENNReal.ofReal K)
    (h_ae_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (X_lim ω))) :
    Integrable X_lim μ ∧ ∫ ω, X_lim ω ∂μ ≤ K := by
  have h_fatou : ∫⁻ ω, ENNReal.ofReal (X_lim ω) ∂μ ≤ ENNReal.ofReal K := by
    have h_fatou_liminf :
        ∫⁻ ω, ENNReal.ofReal (X_lim ω) ∂μ ≤
          Filter.liminf (fun n => ∫⁻ ω, ENNReal.ofReal (X n ω) ∂μ) Filter.atTop := by
      have h_liminf : ∫⁻ ω, ENNReal.ofReal (X_lim ω) ∂μ ≤
          ∫⁻ ω, Filter.liminf (fun n => ENNReal.ofReal (X n ω)) Filter.atTop ∂μ := by
        refine' MeasureTheory.lintegral_mono_ae _
        filter_upwards [h_ae_lim] with ω hω using by
          simpa using Filter.Tendsto.liminf_eq (ENNReal.tendsto_ofReal hω) |> ge_of_eq
      refine' le_trans h_liminf (MeasureTheory.lintegral_liminf_le' _)
      exact fun n => (h_meas n |> Measurable.ennreal_ofReal |> Measurable.aemeasurable)
    refine' le_trans h_fatou_liminf _
    refine' Filter.liminf_le_of_frequently_le _ _
    · exact (Filter.Eventually.of_forall fun n => (h_lintegral_bound n).le).frequently
    · exact ⟨0, Filter.Eventually.of_forall fun _ => zero_le⟩
  have hK_pos : 0 < K := by
    exact ENNReal.ofReal_pos.mp <| lt_of_le_of_lt zero_le (h_lintegral_bound 0)
  have h_nonneg_lim : ∀ᵐ ω ∂μ, 0 ≤ X_lim ω := by
    filter_upwards [h_ae_lim] with ω hω using
      le_of_tendsto_of_tendsto' tendsto_const_nhds hω fun n => h_nonneg n ω
  have h_integrable : Integrable X_lim μ := by
    refine' ⟨_, _⟩
    · exact aestronglyMeasurable_of_tendsto_ae _
        (fun n => (h_meas n).aemeasurable.aestronglyMeasurable) h_ae_lim
    · rw [hasFiniteIntegral_iff_norm]
      refine' lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae _) (lt_of_le_of_lt h_fatou _)
      · filter_upwards [h_nonneg_lim] with ω hω using by rw [Real.norm_of_nonneg hω]
      · exact ENNReal.ofReal_lt_top
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
  · refine ⟨h_integrable, ?_⟩
    have h_toReal :
        (∫⁻ ω, ENNReal.ofReal (X_lim ω) ∂μ).toReal ≤ (ENNReal.ofReal K).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h_fatou
    have hK_nonneg : 0 ≤ K := hK_pos.le
    rw [ENNReal.toReal_ofReal hK_nonneg] at h_toReal
    exact h_toReal
  · exact h_nonneg_lim
  · exact h_integrable.1
