/-
TASK ID: prob_7_6
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open Filter MeasureTheory Topology

private lemma negPart_sub_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b)⁻ ≤ b := by
  rw [negPart_def]
  exact max_le (by linarith) hb

private lemma abs_eq_add_two_negPart (x : ℝ) : |x| = x + 2 * x⁻ := by
  rcases le_or_gt 0 x with h | h
  · simp [abs_of_nonneg h, negPart_eq_zero.mpr h]
  · simp [abs_of_neg h, negPart_eq_neg.mpr h.le]; ring

private lemma negPart_tendsto_zero_of_tendsto {x : ℕ → ℝ} {L : ℝ}
    (h : Tendsto x atTop (𝓝 L)) :
    Tendsto (fun n => (x n - L)⁻) atTop (𝓝 0) := by
  have hsub : Tendsto (fun n => x n - L) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = L - L from by ring]
    exact h.sub tendsto_const_nhds
  have hcont : Continuous (negPart : ℝ → ℝ) := continuous_negPart
  have : Tendsto (fun n => (x n - L)⁻) atTop (𝓝 (0 : ℝ)⁻) :=
    (hcont.tendsto 0).comp hsub
  simpa [negPart_eq_zero.mpr (le_refl (0 : ℝ))] using this

private lemma integrable_of_nonneg_of_lintegral_lt_top {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {u : Ω → ℝ}
    (hu_aesm : AEStronglyMeasurable u μ)
    (hu_nonneg : ∀ᵐ ω ∂μ, 0 ≤ u ω)
    (hu_lt_top : ∫⁻ ω, ENNReal.ofReal (u ω) ∂μ < ⊤) :
    Integrable u μ := by
  refine ⟨hu_aesm, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono_ae ?_) hu_lt_top
  filter_upwards [hu_nonneg] with ω hω using by rw [Real.norm_of_nonneg hω]

private lemma scheffe_part_a {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {f_final : Ω → ℝ}
    (h_meas : ∀ n, Measurable (f n))
    (h_nonneg : ∀ n, ∀ ω, 0 ≤ f n ω)
    (h_ae_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (f_final ω)))
    (h_f_aesm : AEStronglyMeasurable f_final μ)
    (h_f_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f_final ω)
    (h_integrable_f : Integrable f_final μ) :
    Tendsto (fun n => ∫ ω, (f n ω - f_final ω)⁻ ∂μ) atTop (𝓝 0) := by
      convert MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ _
      rw [MeasureTheory.integral_zero]
      use fun ω => f_final ω
      · intro n
        have h_sub_aesm : AEStronglyMeasurable (fun ω => f n ω - f_final ω) μ :=
          ((h_meas n).aemeasurable.sub h_f_aesm.aemeasurable).aestronglyMeasurable
        exact continuous_negPart.comp_aestronglyMeasurable h_sub_aesm
      · exact h_integrable_f
      · intro n
        filter_upwards [h_f_nonneg] with ω hω
        by_cases h : f_final ω ≤ f n ω <;> simp_all +decide [abs_of_nonneg, negPart]
      · filter_upwards [h_ae_conv, h_f_nonneg] with ω hω₁ hω₂ using by
          simpa using negPart_tendsto_zero_of_tendsto hω₁

private lemma scheffe_part_b {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {f_final : Ω → ℝ}
    (h_meas : ∀ n, Measurable (f n))
    (h_nonneg : ∀ n, ∀ ω, 0 ≤ f n ω)
    (h_integrable_fn : ∀ n, Integrable (f n) μ)
    (h_ae_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (f_final ω)))
    (h_f_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f_final ω)
    (h_integrable_f : Integrable f_final μ)
    (h_int_conv : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop (𝓝 (∫ ω, f_final ω ∂μ)))
    (h_part_a : Tendsto (fun n => ∫ ω, (f n ω - f_final ω)⁻ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |f n ω - f_final ω| ∂μ) atTop (𝓝 0) := by
  have h_eq :
      (fun n => ∫ ω, |f n ω - f_final ω| ∂μ) =
        fun n =>
          (∫ ω, f n ω ∂μ) - (∫ ω, f_final ω ∂μ) +
            (∫ ω, (f n ω - f_final ω)⁻ ∂μ) * 2 := by
    funext n
    have hsub : Integrable (fun ω => f n ω - f_final ω) μ :=
      MeasureTheory.Integrable.sub (h_integrable_fn n) h_integrable_f
    have hneg : Integrable (fun ω => (f n ω - f_final ω)⁻) μ :=
      MeasureTheory.Integrable.neg_part hsub
    calc
      ∫ ω, |f n ω - f_final ω| ∂μ =
          ∫ ω, (f n ω - f_final ω) + 2 * (f n ω - f_final ω)⁻ ∂μ := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => by
          simpa using abs_eq_add_two_negPart (f n ω - f_final ω)
      _ = (∫ ω, f n ω - f_final ω ∂μ) +
          ∫ ω, 2 * (f n ω - f_final ω)⁻ ∂μ := by
        rw [MeasureTheory.integral_add hsub (hneg.const_mul 2)]
      _ = (∫ ω, f n ω ∂μ) - (∫ ω, f_final ω ∂μ) +
          2 * (∫ ω, (f n ω - f_final ω)⁻ ∂μ) := by
        rw [MeasureTheory.integral_sub (h_integrable_fn n) h_integrable_f,
          MeasureTheory.integral_const_mul]
      _ = (∫ ω, f n ω ∂μ) - (∫ ω, f_final ω ∂μ) +
          (∫ ω, (f n ω - f_final ω)⁻ ∂μ) * 2 := by
        ring
  simpa [h_eq, mul_comm, sub_self] using
    Tendsto.add (h_int_conv.sub_const (∫ ω, f_final ω ∂μ)) (h_part_a.const_mul 2)

theorem prob_7_6 {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {f_final : Ω → ℝ}
    (h_meas : ∀ n, Measurable (f n))
    (h_nonneg : ∀ n, ∀ ω, 0 ≤ f n ω)
    (h_ae_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (f_final ω)))
    (h_fn_lintegral_lt_top : ∀ n, ∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ < ⊤)
    (h_f_lintegral_lt_top : ∫⁻ ω, ENNReal.ofReal (f_final ω) ∂μ < ⊤)
    (h_lintegral_conv :
      Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (f_final ω) ∂μ))) :
    Tendsto (fun n => ∫ ω, (f n ω - f_final ω)⁻ ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ ω, |f n ω - f_final ω| ∂μ) atTop (𝓝 0) := by
  have h_f_nonneg : ∀ᵐ ω ∂μ, 0 ≤ f_final ω := by
    filter_upwards [h_ae_conv] with ω hω using
      le_of_tendsto_of_tendsto' tendsto_const_nhds hω fun n => h_nonneg n ω
  have h_f_aesm : AEStronglyMeasurable f_final μ :=
    aestronglyMeasurable_of_tendsto_ae _
      (fun n => (h_meas n).aemeasurable.aestronglyMeasurable) h_ae_conv
  have h_integrable_fn : ∀ n, Integrable (f n) μ := by
    intro n
    exact integrable_of_nonneg_of_lintegral_lt_top
      ((h_meas n).aemeasurable.aestronglyMeasurable)
      (Filter.Eventually.of_forall (h_nonneg n))
      (h_fn_lintegral_lt_top n)
  have h_integrable_f : Integrable f_final μ := by
    exact integrable_of_nonneg_of_lintegral_lt_top h_f_aesm h_f_nonneg h_f_lintegral_lt_top
  have h_int_conv : Tendsto (fun n => ∫ ω, f n ω ∂μ) atTop
      (𝓝 (∫ ω, f_final ω ∂μ)) := by
    have h_toReal_conv :=
      (ENNReal.tendsto_toReal h_f_lintegral_lt_top.ne).comp h_lintegral_conv
    have h_eq_n :
        (fun n => ∫ ω, f n ω ∂μ) =
          fun n => (∫⁻ ω, ENNReal.ofReal (f n ω) ∂μ).toReal := by
      funext n
      exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (h_nonneg n)) (h_integrable_fn n).aestronglyMeasurable
    have h_eq_final :
        ∫ ω, f_final ω ∂μ = (∫⁻ ω, ENNReal.ofReal (f_final ω) ∂μ).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_f_nonneg
        h_integrable_f.aestronglyMeasurable
    rw [h_eq_n, h_eq_final]
    exact h_toReal_conv
  have ha := scheffe_part_a h_meas h_nonneg h_ae_conv h_f_aesm h_f_nonneg h_integrable_f
  exact ⟨ha, scheffe_part_b h_meas h_nonneg h_integrable_fn h_ae_conv h_f_nonneg
    h_integrable_f h_int_conv ha⟩
