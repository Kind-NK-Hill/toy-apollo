/-
TASK ID: thm_7_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import ProbabilityTheory.chapter_06.thm_6_4







-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory



theorem thm_7_3 {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) (X : ℕ → Ω → ENNReal)
  (hX : ∀ n, Measurable (X n)) :
    ∫⁻ ω, Filter.liminf (fun n => X n ω) Filter.atTop ∂μ ≤
      Filter.liminf (fun n => ∫⁻ ω, X n ω ∂μ) Filter.atTop
  := by
  let Y : ℕ → Ω → ENNReal := fun n ω => ⨅ k, ⨅ (_ : n ≤ k), X k ω
  have hY_meas : ∀ n, Measurable (Y n) := by
    intro n
    exact Measurable.iInf fun k => Measurable.iInf fun _ => hX k
  have hY_mono : Monotone Y := by
    intro m n hmn ω
    apply le_iInf
    intro k
    apply le_iInf
    intro hnk
    exact iInf_le_of_le k (iInf_le_of_le (hmn.trans hnk) le_rfl)
  have hY_sup : ∀ ω, (⨆ n, Y n ω) =
      Filter.liminf (fun n => X n ω) Filter.atTop := by
    intro ω
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
  have hMCT := thm_6_4 μ Y
    (fun ω => Filter.liminf (fun n => X n ω) Filter.atTop)
    hY_meas hY_mono hY_sup
  have h_integral_mono : Monotone (fun n => ∫⁻ ω, Y n ω ∂μ) := by
    intro m n hmn
    exact lintegral_mono fun ω => hY_mono hmn ω
  have h_integral_sup :
      (⨆ n, ∫⁻ ω, Y n ω ∂μ) =
        ∫⁻ ω, Filter.liminf (fun n => X n ω) Filter.atTop ∂μ := by
    exact tendsto_nhds_unique (tendsto_atTop_iSup h_integral_mono) hMCT
  have h_tail_integral (n : ℕ) :
      (∫⁻ ω, Y n ω ∂μ) ≤ ⨅ k, ⨅ (_ : n ≤ k), ∫⁻ ω, X k ω ∂μ := by
    apply le_iInf
    intro k
    apply le_iInf
    intro hnk
    exact lintegral_mono fun ω => iInf_le_of_le k (iInf_le_of_le hnk le_rfl)
  calc
    ∫⁻ ω, Filter.liminf (fun n => X n ω) Filter.atTop ∂μ =
        ⨆ n, ∫⁻ ω, Y n ω ∂μ := h_integral_sup.symm
    _ ≤ ⨆ n, ⨅ k, ⨅ (_ : n ≤ k), ∫⁻ ω, X k ω ∂μ := by
      exact iSup_mono h_tail_integral
    _ = Filter.liminf (fun n => ∫⁻ ω, X n ω ∂μ) Filter.atTop :=
      Filter.liminf_eq_iSup_iInf_of_nat.symm
