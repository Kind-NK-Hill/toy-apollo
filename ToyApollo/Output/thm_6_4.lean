/-
TASK ID: thm_6_4
TYPE: Theorem_with_Proof
SOURCE PLAN: 20_chap6_nonnegative_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter

theorem thm_6_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Xn : ℕ → Ω → ENNReal)
    (X : Ω → ENNReal) (h_meas : ∀ n, Measurable (Xn n)) (h_mono : Monotone Xn)
    (h_sup : ∀ ω, (⨆ n, Xn n ω) = X ω) :
    Tendsto (fun n => ∫⁻ ω, Xn n ω ∂μ) atTop (nhds (∫⁻ ω, X ω ∂μ)) := by
  have h_int_mono : Monotone fun n => ∫⁻ ω, Xn n ω ∂μ := by
    intro m n hmn
    exact MeasureTheory.lintegral_mono (fun ω => h_mono hmn ω)
  have h_lintegral :
      ∫⁻ ω, X ω ∂μ = ⨆ n, ∫⁻ ω, Xn n ω ∂μ := by
    calc
      ∫⁻ ω, X ω ∂μ = ∫⁻ ω, ⨆ n, Xn n ω ∂μ := by simp [h_sup]
      _ = ⨆ n, ∫⁻ ω, Xn n ω ∂μ := MeasureTheory.lintegral_iSup h_meas h_mono
  rw [h_lintegral]
  exact tendsto_atTop_iSup h_int_mono
