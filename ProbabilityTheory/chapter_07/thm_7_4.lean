/-
TASK ID: thm_7_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import ProbabilityTheory.chapter_06.thm_6_6
import ProbabilityTheory.chapter_07.thm_7_1








open Filter MeasureTheory



theorem thm_7_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X Y : Ω → ℝ)
    (hXm : ∀ n, AEStronglyMeasurable (Xn n) μ)
    (hYint : Integrable Y μ)
    (h_bound : ∀ n, ∀ᵐ ω ∂μ, ‖Xn n ω‖ ≤ Y ω)
    (h_lim : ∀ᵐ ω ∂μ, Tendsto (fun n => Xn n ω) atTop (nhds (X ω))) :
  Integrable X μ ∧
    Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) := by
  have hX_meas : AEStronglyMeasurable X μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hXm h_lim
  have h_bound_all : ∀ᵐ ω ∂μ, ∀ n, ‖Xn n ω‖ ≤ Y ω :=
    eventually_countable_forall.2 h_bound
  have hX_bound : ∀ᵐ ω ∂μ, ‖X ω‖ ≤ Y ω := by
    filter_upwards [h_bound_all, h_lim] with ω hω_bound hω_lim
    have hnorm_tendsto : Tendsto (fun n => ‖Xn n ω‖) atTop (nhds ‖X ω‖) :=
      (continuous_norm.tendsto (X ω)).comp hω_lim
    have hmem : ∀ᶠ n in atTop, ‖Xn n ω‖ ∈ Set.Iic (Y ω) :=
      Filter.Eventually.of_forall fun n => hω_bound n
    have hlimit_mem : ‖X ω‖ ∈ Set.Iic (Y ω) :=
      IsClosed.mem_of_tendsto isClosed_Iic hnorm_tendsto hmem
    simpa [Set.mem_Iic] using hlimit_mem
  have hX_int : Integrable X μ :=
    Integrable.mono' hYint hX_meas hX_bound
  have hXn_int : ∀ n, Integrable (Xn n) μ := fun n =>
    Integrable.mono' hYint (hXm n) (h_bound n)
  have hdiff_int : ∀ n, Integrable (fun ω => ‖Xn n ω - X ω‖) μ := fun n =>
    ((hXn_int n).sub hX_int).norm
  have hY_nonneg : 0 ≤ᵐ[μ] Y := by
    filter_upwards [h_bound 0] with ω hω
    exact (norm_nonneg (Xn 0 ω)).trans hω
  have hdiff_le : ∀ n, ∀ᵐ ω ∂μ, ‖Xn n ω - X ω‖ ≤ (2 : ℝ) * Y ω := by
    intro n
    filter_upwards [h_bound n, hX_bound] with ω hn hX
    calc
      ‖Xn n ω - X ω‖ ≤ ‖Xn n ω‖ + ‖X ω‖ := norm_sub_le _ _
      _ ≤ Y ω + Y ω := add_le_add hn hX
      _ = (2 : ℝ) * Y ω := by ring
  have hdiff_lim :
      ∀ᵐ ω ∂μ, Tendsto (fun n => ‖Xn n ω - X ω‖) atTop (nhds 0) := by
    filter_upwards [h_lim] with ω hω
    have hsub : Tendsto (fun n => Xn n ω - X ω) atTop (nhds 0) := by
      simpa using hω.sub_const (X ω)
    simpa using hsub.norm
  have htwoY_int : Integrable (fun ω => (2 : ℝ) * Y ω) μ :=
    hYint.const_mul 2
  have htwoY_nonneg : ∀ᵐ ω ∂μ, 0 ≤ (2 : ℝ) * Y ω := by
    filter_upwards [hY_nonneg] with ω hω
    exact mul_nonneg (by norm_num) hω
  have hfatou_meas : ∀ n, AEMeasurable
      (fun ω => ENNReal.ofReal ((2 : ℝ) * Y ω - ‖Xn n ω - X ω‖)) μ := by
    intro n
    exact (htwoY_int.sub (hdiff_int n)).aemeasurable.ennreal_ofReal
  have hfatou_lim : ∀ᵐ ω ∂μ, Tendsto
      (fun n => ENNReal.ofReal ((2 : ℝ) * Y ω - ‖Xn n ω - X ω‖))
      atTop (nhds (ENNReal.ofReal ((2 : ℝ) * Y ω))) := by
    filter_upwards [hdiff_lim] with ω hω
    exact ENNReal.tendsto_ofReal (by simpa using hω.const_sub ((2 : ℝ) * Y ω))
  have hdiff_lintegral_ne_top : ∀ n,
      (∫⁻ ω, ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ) ≠ (⊤ : ENNReal) := fun n =>
    (hdiff_int n).lintegral_lt_top.ne
  have htwoY_lintegral_ne_top :
      (∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω) ∂μ) ≠ (⊤ : ENNReal) :=
    htwoY_int.lintegral_lt_top.ne
  have hfatou_integral : ∀ n,
      (∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω - ‖Xn n ω - X ω‖) ∂μ) =
        (∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω) ∂μ) -
          ∫⁻ ω, ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ := by
    intro n
    calc
      (∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω - ‖Xn n ω - X ω‖) ∂μ) =
          ∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω) -
            ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ := by
              apply MeasureTheory.lintegral_congr_ae
              filter_upwards [hdiff_le n] with ω hω
              exact ENNReal.ofReal_sub _ (norm_nonneg _)
      _ = (∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω) ∂μ) -
            ∫⁻ ω, ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ := by
              apply MeasureTheory.lintegral_sub'
              · exact (hdiff_int n).aemeasurable.ennreal_ofReal
              · exact hdiff_lintegral_ne_top n
              · filter_upwards [hdiff_le n] with ω hω
                exact ENNReal.ofReal_le_ofReal hω
  have hfatou :
      (∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω) ∂μ) ≤
        Filter.liminf
          (fun n => ∫⁻ ω,
            ENNReal.ofReal ((2 : ℝ) * Y ω - ‖Xn n ω - X ω‖) ∂μ)
          atTop := by
    calc
      (∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω) ∂μ) =
          ∫⁻ ω, Filter.liminf
            (fun n => ENNReal.ofReal ((2 : ℝ) * Y ω - ‖Xn n ω - X ω‖))
            atTop ∂μ := by
              apply MeasureTheory.lintegral_congr_ae
              filter_upwards [hfatou_lim] with ω hω
              exact hω.liminf_eq.symm
      _ ≤ Filter.liminf
          (fun n => ∫⁻ ω,
            ENNReal.ofReal ((2 : ℝ) * Y ω - ‖Xn n ω - X ω‖) ∂μ)
          atTop := MeasureTheory.lintegral_liminf_le' hfatou_meas
  have hdiff_lintegral_le : ∀ n,
      (∫⁻ ω, ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ) ≤
        ∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω) ∂μ := by
    intro n
    exact MeasureTheory.lintegral_mono_ae <| by
      filter_upwards [hdiff_le n] with ω hω
      exact ENNReal.ofReal_le_ofReal hω
  have hdiff_limsup_le :
      Filter.limsup
          (fun n => ∫⁻ ω, ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ) atTop ≤
        ∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω) ∂μ :=
    Filter.limsup_le_of_le (h := Filter.Eventually.of_forall hdiff_lintegral_le)
  rw [Filter.liminf_congr (Filter.Eventually.of_forall hfatou_integral),
    ENNReal.liminf_const_sub atTop
      (fun n => ∫⁻ ω, ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ)
      htwoY_lintegral_ne_top] at hfatou
  have hdiff_limsup_eq_zero :
      Filter.limsup
          (fun n => ∫⁻ ω, ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ) atTop = 0 := by
    by_cases hzero : (∫⁻ ω, ENNReal.ofReal ((2 : ℝ) * Y ω) ∂μ) = 0
    · apply le_antisymm
      · exact hdiff_limsup_le.trans_eq hzero
      · exact bot_le
    · apply le_antisymm
      · by_contra hnot
        have hne : Filter.limsup
            (fun n => ∫⁻ ω, ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ) atTop ≠ 0 := by
          intro heq
          exact hnot heq.le
        have hlt := ENNReal.sub_lt_self htwoY_lintegral_ne_top hzero hne
        exact (not_lt_of_ge hfatou) hlt
      · exact bot_le
  have hdiff_lintegral_tendsto :
      Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ)
        atTop (nhds 0) :=
    tendsto_of_le_liminf_of_limsup_le bot_le (by simpa [hdiff_limsup_eq_zero])
  have hdiff_integral_tendsto :
      Tendsto (fun n => ∫ ω, ‖Xn n ω - X ω‖ ∂μ) atTop (nhds 0) := by
    have hrepr : ∀ n,
        (∫ ω, ‖Xn n ω - X ω‖ ∂μ) =
          (∫⁻ ω, ENNReal.ofReal (‖Xn n ω - X ω‖) ∂μ).toReal := by
      intro n
      exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω => norm_nonneg _) (hdiff_int n).aestronglyMeasurable
    have htoReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      hdiff_lintegral_tendsto
    simpa only [hrepr, Function.comp_def, ENNReal.toReal_zero] using htoReal
  have h_tendsto :
      Tendsto (fun n => ∫ ω, Xn n ω ∂μ) atTop (nhds (∫ ω, X ω ∂μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) _ hdiff_integral_tendsto
    intro n
    rw [← MeasureTheory.integral_sub (hXn_int n) hX_int]
    exact thm_7_1 μ (fun ω => Xn n ω - X ω) ((hXn_int n).sub hX_int)
  exact ⟨hX_int, h_tendsto⟩
