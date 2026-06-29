/-
TASK ID: thm_10_9
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-random-vectors
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_2_8

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem coordinatewiseMeasurable_iff_vectorMeasurable {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (V : Ω → Fin d → ℝ) :
    Measurable V ↔ ∀ i : Fin d, Measurable (fun ω : Ω => V ω i) := by
  exact measurable_pi_iff

theorem thm_10_9 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (V : Ω → Fin d → ℝ) :
    Measurable V ↔ ∀ i : Fin d, Measurable (fun ω : Ω => V ω i) := by
  exact coordinatewiseMeasurable_iff_vectorMeasurable V
