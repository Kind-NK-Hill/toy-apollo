/-
TASK ID: thm_7_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
-- supplies the canonical Borel `MeasurableSpace` for
-- an abstract `RCLike 𝕜`, as well as measurability of the
--norm and `ENNReal.ofReal`.








open MeasureTheory



theorem thm_7_2 {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜] {μ : Measure Ω}
    {X : Ω → 𝕜} (hX : Measurable X) :
    (∫⁻ ω, ENNReal.ofReal ‖X ω‖ ∂μ = 0) ↔ X =ᵐ[μ] 0 := by
  let nX : Ω → ENNReal := fun ω => ENNReal.ofReal ‖X ω‖
  constructor
  · intro h_zero
    let E : ℕ → Set Ω := fun n => {ω | (1 / (n + 1 : ℝ)) ≤ ‖X ω‖}
    have hE_meas : ∀ n, MeasurableSet (E n) := by
      intro n
      change MeasurableSet ((fun ω => ‖X ω‖) ⁻¹' Set.Ici (1 / (n + 1 : ℝ)))
      exact hX.norm measurableSet_Ici
    have hE_null : ∀ n, μ (E n) = 0 := by
      intro n
      let c : ENNReal := ENNReal.ofReal (1 / (n + 1 : ℝ))
      have h_lower : (E n).indicator (fun _ => c) ≤ nX := by
        intro ω
        by_cases hω : ω ∈ E n
        · rw [Set.indicator_of_mem hω]
          exact ENNReal.ofReal_le_ofReal hω
        · rw [Set.indicator_of_notMem hω]
          exact bot_le
      have h_indicator_zero : ∫⁻ ω, (E n).indicator (fun _ => c) ω ∂μ = 0 := by
        apply nonpos_iff_eq_zero.mp
        calc
          ∫⁻ ω, (E n).indicator (fun _ => c) ω ∂μ ≤ ∫⁻ ω, nX ω ∂μ :=
            lintegral_mono h_lower
          _ = 0 := by simpa [nX] using h_zero
      have hc_ne_zero : c ≠ 0 := by
        exact ENNReal.ofReal_ne_zero_iff.mpr (one_div_pos.mpr (by positivity))
      rw [lintegral_indicator_const (hE_meas n)] at h_indicator_zero
      exact (mul_eq_zero.mp h_indicator_zero).resolve_left hc_ne_zero
    have h_cover : {ω | X ω ≠ 0} ⊆ ⋃ n, E n := by
      intro ω hω
      have hnorm_pos : 0 < ‖X ω‖ := norm_pos_iff.mpr hω
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hnorm_pos
      exact Set.mem_iUnion.2 ⟨n, hn.le⟩
    apply ae_iff.2
    change μ {ω | X ω ≠ 0} = 0
    exact measure_mono_null h_cover (measure_iUnion_null hE_null)
  · intro hX_zero
    calc
      ∫⁻ ω, ENNReal.ofReal ‖X ω‖ ∂μ = ∫⁻ ω, 0 ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hX_zero] with ω hω
        simp [hω]
      _ = 0 := lintegral_zero
