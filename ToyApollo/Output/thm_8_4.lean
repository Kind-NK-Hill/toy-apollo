/-
TASK ID: thm_8_4
TYPE: Theorem_with_Proof
SOURCE PLAN: 32_chap8_product_measure_fubini
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

noncomputable section

theorem thm_8_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY_meas : Measurable Y) (hY_int : Integrable Y P) (hY_nn : 0 ≤ᵐ[P] Y) :
    (∫ ω, Y ω ∂P = ∫ u in Set.Ioi 0, P.real {ω : Ω | u ≤ Y ω}) ∧
      ∀ FY : ℝ → ℝ, (∀ u : ℝ, FY u = P.real {ω : Ω | Y ω < u}) →
        ∫ ω, Y ω ∂P = ∫ u in Set.Ioi 0, (1 - FY u) := by
  refine ⟨hY_int.integral_eq_integral_meas_le hY_nn, ?_⟩
  intro FY hFY
  rw [hY_int.integral_eq_integral_meas_le hY_nn]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hs : MeasurableSet {ω : Ω | Y ω < u} := measurableSet_lt hY_meas measurable_const
  have hcompl : P.real {ω : Ω | u ≤ Y ω} = 1 - P.real {ω : Ω | Y ω < u} := by
    simpa [Set.compl_setOf, not_lt] using
      (MeasureTheory.probReal_compl_eq_one_sub (μ := P) hs)
  rw [hcompl, hFY u]
