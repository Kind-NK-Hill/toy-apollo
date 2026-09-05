/-
TASK ID: thm_13_16
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.thm_13_15




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section



theorem thm_13_16_integral_eq_of_condExp {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : MeasurableSpace Ω} (h𝓖 : 𝓖 ≤ 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X Y : Ω → ℝ}
    (hCE : P[X | 𝓖] =ᵐ[P] Y) :
    ∫ ω, X ω ∂P = ∫ ω, Y ω ∂P := by
  calc
    ∫ ω, X ω ∂P = ∫ ω, P[X | 𝓖] ω ∂P := (integral_condExp h𝓖).symm
    _ = ∫ ω, Y ω ∂P := integral_congr_ae hCE



theorem thm_13_16_condExp_zero {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X) (n : ℕ) :
    P[X n | 𝓕n 0] =ᵐ[P] X 0 := by
  exact (thm_13_15_multiStep_of_martingale hM
    0 n (Nat.zero_le n)).condExp_eq



theorem thm_13_16 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X) :
    ∀ n : ℕ, 1 ≤ n → ∫ ω, X n ω ∂P = ∫ ω, X 0 ω ∂P := by
  intro n _hn
  exact thm_13_15_expectation_constant hM n
