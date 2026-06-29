/-
TASK ID: thm_10_3
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-almost-sure-probability
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem thm_10_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (h_nonneg : 0 ≤ᵐ[P] X) (h_int : Integrable X P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω : Ω | ε ≤ X ω} ≤ (∫ ω, X ω ∂P) / ε := by
  have hmul := MeasureTheory.mul_meas_ge_le_integral_of_nonneg h_nonneg h_int ε
  rw [le_div_iff₀ hε]
  simpa [mul_comm] using hmul
