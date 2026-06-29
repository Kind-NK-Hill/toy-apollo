/-
TASK ID: thm_7_3
TYPE: Theorem_with_Proof
SOURCE PLAN: 26_chap7_fatou_dct
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import ToyApollo.Output.thm_6_4

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem thm_7_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ENNReal)
    (hX : ∀ n, Measurable (X n)) :
    ∫⁻ ω, Filter.liminf (fun n => X n ω) Filter.atTop ∂μ ≤
      Filter.liminf (fun n => ∫⁻ ω, X n ω ∂μ) Filter.atTop := by
  simpa using (MeasureTheory.lintegral_liminf_le (μ := μ) hX)
