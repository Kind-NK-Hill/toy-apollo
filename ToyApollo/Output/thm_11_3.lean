/-
TASK ID: thm_11_3
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-bounds-inequalities
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_4_1
import ToyApollo.Output.thm_6_7__lemma_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

theorem thm_11_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {φ : ℝ → ℝ} {X : Ω → ℝ}
    (hXrv : IsRealMeasurable X) (hφ : ConvexOn ℝ Set.univ φ) (hX : Integrable X P)
    (hφX : Integrable (φ ∘ X) P) :
    φ (P[X]) ≤ P[fun ω => φ (X ω)] := by
  have _ : Measurable X := hXrv
  have hφc : ContinuousOn φ Set.univ := hφ.continuousOn isOpen_univ
  have hXmem : ∀ᵐ ω ∂P, X ω ∈ (Set.univ : Set ℝ) := by simp
  exact ConvexOn.map_integral_le hφ hφc isClosed_univ hXmem hX hφX

theorem thm_11_3_textbook_expectation_bridge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {φ : ℝ → ℝ} {X : Ω → ℝ}
    (hXrv : IsRealMeasurable X) (hφX_meas : Measurable (fun ω => φ (X ω)))
    (hφ : ConvexOn ℝ Set.univ φ) (hX : Integrable X P)
    (hφX : Integrable (φ ∘ X) P) :
    expectation P (fun ω => (X ω : EReal)) = some (Real.toEReal (P[X])) ∧
      expectation P (fun ω => (φ (X ω) : EReal)) =
        some (Real.toEReal (P[fun ω => φ (X ω)])) ∧
      φ (P[X]) ≤ P[fun ω => φ (X ω)] := by
  have hX_meas : Measurable X := hXrv
  refine ⟨?_, ?_, ?_⟩
  · exact chapter6_expectation_real_eq_integral (P := P) (f := X) hX_meas hX
  · exact chapter6_expectation_real_eq_integral (P := P) (f := fun ω => φ (X ω))
      hφX_meas hφX
  · exact thm_11_3 P hXrv hφ hX hφX
