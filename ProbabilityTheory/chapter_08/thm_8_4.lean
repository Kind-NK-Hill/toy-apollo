/-
TASK ID: thm_8_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake









open MeasureTheory Set

noncomputable section



theorem thm_8_4_lintegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY_meas : Measurable Y) :
    ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P = ∫⁻ u in Set.Ioi 0, P {ω : Ω | u ≤ Y ω} := by
  let K : ℝ × Ω → ENNReal := fun p =>
    ({q : ℝ × Ω | 0 < q.1 ∧ q.1 ≤ Y q.2} : Set (ℝ × Ω)).indicator (fun _ => 1) p
  have hK_meas : Measurable K := by
    apply measurable_const.indicator
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (hY_meas.comp measurable_snd))
  have h_tail_inner (u : ℝ) :
      ∫⁻ ω, K (u, ω) ∂P =
        (Set.Ioi (0 : ℝ)).indicator (fun v => P {ω : Ω | v ≤ Y ω}) u := by
    by_cases hu : 0 < u
    · have h_event : MeasurableSet {ω : Ω | u ≤ Y ω} :=
        measurableSet_le measurable_const hY_meas
      have h_slice : (fun ω => K (u, ω)) =
          {ω : Ω | u ≤ Y ω}.indicator (1 : Ω → ENNReal) := by
        funext ω
        by_cases hω : u ≤ Y ω <;> simp [K, hu, hω]
      rw [h_slice, MeasureTheory.lintegral_indicator_one h_event]
      simp [hu]
    · have h_slice : (fun ω => K (u, ω)) = 0 := by
        funext ω
        simp [K, hu]
      rw [h_slice]
      rw [show (Set.Ioi (0 : ℝ)).indicator
        (fun v => P {ω : Ω | v ≤ Y ω}) u = 0 by simp [hu]]
      exact MeasureTheory.lintegral_zero_fun
  have h_interval_inner (ω : Ω) :
      ∫⁻ u, K (u, ω) ∂(volume : Measure ℝ) = ENNReal.ofReal (Y ω) := by
    have h_slice : (fun u => K (u, ω)) =
        (Set.Ioc (0 : ℝ) (Y ω)).indicator (1 : ℝ → ENNReal) := by
      funext u
      by_cases hu : 0 < u ∧ u ≤ Y ω <;> simp [K, Set.mem_Ioc, hu]
    rw [h_slice, MeasureTheory.lintegral_indicator_one measurableSet_Ioc,
      Real.volume_Ioc]
    simp
  have hK_ae : AEMeasurable (Function.uncurry fun u ω => K (u, ω))
      ((volume : Measure ℝ).prod P) := by
    rw [show Function.uncurry (fun u ω => K (u, ω)) = K by
      funext p
      rcases p with ⟨u, ω⟩
      rfl]
    exact hK_meas.aemeasurable
  calc
    ∫⁻ ω, ENNReal.ofReal (Y ω) ∂P =
        ∫⁻ ω, ∫⁻ u, K (u, ω) ∂(volume : Measure ℝ) ∂P := by
          apply lintegral_congr
          exact fun ω => (h_interval_inner ω).symm
    _ = ∫⁻ u, ∫⁻ ω, K (u, ω) ∂P ∂(volume : Measure ℝ) := by
      exact (MeasureTheory.lintegral_lintegral_swap
        (μ := (volume : Measure ℝ)) (ν := P) hK_ae).symm
    _ = ∫⁻ u, (Set.Ioi (0 : ℝ)).indicator
        (fun v => P {ω : Ω | v ≤ Y ω}) u ∂(volume : Measure ℝ) := by
          apply lintegral_congr
          exact h_tail_inner
    _ = ∫⁻ u in Set.Ioi 0, P {ω : Ω | u ≤ Y ω} := by
      exact MeasureTheory.lintegral_indicator (μ := (volume : Measure ℝ)) measurableSet_Ioi
        (fun v => P {ω : Ω | v ≤ Y ω})



theorem thm_8_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY_meas : Measurable Y) (hY_int : Integrable Y P) (hY_nn : 0 ≤ᵐ[P] Y) :
    (∫ ω, Y ω ∂P = ∫ u in Set.Ioi 0, P.real {ω : Ω | u ≤ Y ω}) ∧
      ∀ FY : ℝ → ℝ, (∀ u : ℝ, FY u = P.real {ω : Ω | Y ω < u}) →
        ∫ ω, Y ω ∂P = ∫ u in Set.Ioi 0, (1 - FY u) := by
  have h_layer_lintegral := thm_8_4_lintegral P hY_meas
  have h_tail_meas : Measurable (fun u : ℝ => P.real {ω : Ω | u ≤ Y ω}) := by
    apply Measurable.ennreal_toReal
    apply Antitone.measurable
    intro a b hab
    exact measure_mono fun ω hω => hab.trans hω
  have h_tail_real :
      ∫ u in Set.Ioi 0, P.real {ω : Ω | u ≤ Y ω} =
        ENNReal.toReal (∫⁻ u in Set.Ioi 0, P {ω : Ω | u ≤ Y ω}) := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro u _
      exact ENNReal.ofReal_toReal (measure_ne_top P _)
    · exact Filter.Eventually.of_forall fun _ => measureReal_nonneg
    · exact h_tail_meas.aestronglyMeasurable
  have h_layer :
      ∫ ω, Y ω ∂P = ∫ u in Set.Ioi 0, P.real {ω : Ω | u ≤ Y ω} := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      hY_nn hY_int.aestronglyMeasurable, h_tail_real]
    exact congrArg ENNReal.toReal h_layer_lintegral
  refine ⟨h_layer, ?_⟩
  intro FY hFY
  rw [h_layer]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hs : MeasurableSet {ω : Ω | Y ω < u} :=
    measurableSet_lt hY_meas measurable_const
  have hcompl : P.real {ω : Ω | u ≤ Y ω} = 1 - P.real {ω : Ω | Y ω < u} := by
    simpa [Set.compl_setOf, not_lt] using
      (MeasureTheory.probReal_compl_eq_one_sub (μ := P) hs)
  rw [hcompl, hFY u]
