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
  let A : Set Ω := {ω : Ω | ε ≤ X ω}
  have hA : NullMeasurableSet A P := by
    change NullMeasurableSet (X ⁻¹' Set.Ici ε) P
    exact h_int.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici
  have hindicator_nonneg :
      0 ≤ᵐ[P] A.indicator (fun _ : Ω => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ A <;> simp [hω]
  have hindicator_le :
      A.indicator (fun _ : Ω => (1 : ℝ)) ≤ᵐ[P] fun ω => X ω / ε := by
    filter_upwards [h_nonneg] with ω hXω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      exact (le_div_iff₀ hε).2 (by simpa [A] using hω)
    · rw [Set.indicator_of_notMem hω]
      exact div_nonneg hXω hε.le
  have hindicator_expectation :
      (∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) = P.real A := by
    rw [integral_indicator₀ hA, setIntegral_one_eq_measureReal]
  have hscaled_integrable : Integrable (fun ω => X ω / ε) P :=
    h_int.div_const ε
  have hintegral_mono :
      (∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P) ≤
        ∫ ω, X ω / ε ∂P :=
    integral_mono_of_nonneg hindicator_nonneg hscaled_integrable hindicator_le
  change P.real A ≤ (∫ ω, X ω ∂P) / ε
  calc
    P.real A = ∫ ω, A.indicator (fun _ : Ω => (1 : ℝ)) ω ∂P :=
      hindicator_expectation.symm
    _ ≤ ∫ ω, X ω / ε ∂P := hintegral_mono
    _ = (∫ ω, X ω ∂P) / ε := integral_div ε X
