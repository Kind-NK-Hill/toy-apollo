/-
TASK ID: thm_9_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter9-moments-mgf
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_09.def_9_1
import ProbabilityTheory.chapter_09.def_9_2




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

theorem thm_9_2_integrable_exp_mul_of_momentGeneratingFunction_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    {t : ℝ} (ht : momentGeneratingFunction μ X hXm t < ⊤) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    (aemeasurable_exp_mul t hXm)
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)).1
    (by simpa [momentGeneratingFunction] using ht.ne)

theorem thm_9_2_momentGeneratingFunction_toReal_eq_mgf_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    {t : ℝ} (ht : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    (momentGeneratingFunction μ X hXm t).toReal = mgf X μ t := by
  have h_nonneg : 0 ≤ᵐ[μ] fun ω => Real.exp (t * X ω) :=
    Filter.Eventually.of_forall fun _ => Real.exp_nonneg _
  rw [momentGeneratingFunction, mgf,
    ← ofReal_integral_eq_lintegral_ofReal ht h_nonneg]
  exact ENNReal.toReal_ofReal
    (integral_nonneg fun _ => Real.exp_nonneg _)

theorem thm_9_2_mem_interior_integrableExpSet_of_HasMomentGeneratingFunction
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    (hX : HasMomentGeneratingFunction μ X hXm) :
    (0 : ℝ) ∈ interior (integrableExpSet X μ) := by
  rcases hX with ⟨δ, hδ_pos, hδ_fin⟩
  rw [mem_interior]
  refine ⟨Set.Ioo (-δ) δ, ?_, isOpen_Ioo, ?_⟩
  · intro t ht
    exact thm_9_2_integrable_exp_mul_of_momentGeneratingFunction_lt_top hXm
      (hδ_fin t (abs_lt.mpr ht))
  · exact ⟨by linarith, hδ_pos⟩

theorem thm_9_2_momentGeneratingFunction_toReal_eq_mgf_near_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    (hX : HasMomentGeneratingFunction μ X hXm) :
    (fun t => (momentGeneratingFunction μ X hXm t).toReal) =ᶠ[nhds (0 : ℝ)]
      mgf X μ := by
  have hInterior :
      (0 : ℝ) ∈ interior (integrableExpSet X μ) :=
    thm_9_2_mem_interior_integrableExpSet_of_HasMomentGeneratingFunction hXm hX
  filter_upwards [isOpen_interior.eventually_mem hInterior] with t ht
  have htSet : t ∈ integrableExpSet X μ :=
    (show interior (integrableExpSet X μ) ⊆ integrableExpSet X μ from
      interior_subset) ht
  exact thm_9_2_momentGeneratingFunction_toReal_eq_mgf_of_integrable hXm
    htSet

theorem thm_9_2_finiteAbsMoment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXmeas : Measurable X) (hXm : AEMeasurable X μ)
    (hX : HasMomentGeneratingFunction μ X hXm) (n : ℕ) :
    FiniteAbsMoment μ X n := by
  have hInterior :
      (0 : ℝ) ∈ interior (integrableExpSet X μ) :=
    thm_9_2_mem_interior_integrableExpSet_of_HasMomentGeneratingFunction hXm hX
  exact ⟨hXmeas, integrable_pow_abs_of_mem_interior_integrableExpSet hInterior n⟩

theorem thm_9_2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXmeas : Measurable X) (hXm : AEMeasurable X μ)
    (hX : HasMomentGeneratingFunction μ X hXm) (n : ℕ) :
    FiniteAbsMoment μ X n ∧
      generalMoment μ X n (thm_9_2_finiteAbsMoment hXmeas hXm hX n) =
        iteratedDeriv n (mgf X μ) 0 := by
  have hInterior :
      (0 : ℝ) ∈ interior (integrableExpSet X μ) :=
    thm_9_2_mem_interior_integrableExpSet_of_HasMomentGeneratingFunction hXm hX
  constructor
  · exact thm_9_2_finiteAbsMoment hXmeas hXm hX n
  · simpa [generalMoment, moment] using
      (iteratedDeriv_mgf_zero (X := X) (μ := μ) hInterior n).symm
