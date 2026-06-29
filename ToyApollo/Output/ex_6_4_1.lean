/-
TASK ID: ex_6_4_1
TYPE: Example_Proof
SOURCE PLAN: 22_chap6_expectation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_6_7
import ToyApollo.Output.thm_6_7

open MeasureTheory
open scoped BigOperators

-- WRITE FINAL LEAN CODE BELOW

theorem expectation_eq_textbookIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → EReal) :
    expectation P X = textbookIntegral P X := by
  unfold expectation Def67Support.textbookIntegral textbookIntegral
  simp [Def67Support.posLIntegral, Def65Support.posLIntegral,
    Def67Support.negLIntegral, Def65Support.negLIntegral,
    Def67Support.posPart, Def65Support.posPart,
    Def67Support.negPart, Def65Support.negPart]

theorem ex_6_4_1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (s : Finset ℝ) (hXm : Measurable X)
    (hs : ∀ ω, X ω ∈ s) :
    (∀ ω, X ω = ∑ x ∈ s, Set.indicator (X ⁻¹' {x}) (fun _ => x) ω) ∧
      expectation P (fun ω => (X ω : EReal)) =
        some (((∑ x ∈ s, x * P.real (X ⁻¹' {x})) : ℝ) : EReal) := by
  classical
  have hrepr :
      ∀ ω, X ω = ∑ x ∈ s, Set.indicator (X ⁻¹' {x}) (fun _ => x) ω := by
    intro ω
    rw [Finset.sum_eq_single_of_mem (X ω) (hs ω)]
    · simp
    · intro y hy hyne
      have hnot : ω ∉ X ⁻¹' {y} := by
        intro hω
        exact hyne (by simpa using hω.symm)
      simp [Set.indicator, hnot]
  have hterm_integrable :
      ∀ x ∈ s, Integrable (Set.indicator (X ⁻¹' {x}) (fun _ : Ω => x)) P := by
    intro x hx
    exact (integrable_const x).indicator (hXm (measurableSet_singleton x))
  have hX_integrable :
      Integrable X P := by
    have hsum_integrable :
        Integrable (fun ω => ∑ x ∈ s, Set.indicator (X ⁻¹' {x}) (fun _ : Ω => x) ω) P := by
      exact MeasureTheory.integrable_finset_sum s hterm_integrable
    refine hsum_integrable.congr ?_
    exact Filter.Eventually.of_forall fun ω => (hrepr ω).symm
  have hIntegral :
      ∫ ω, X ω ∂P = ∑ x ∈ s, x * P.real (X ⁻¹' {x}) := by
    calc
      ∫ ω, X ω ∂P = ∫ ω, ∑ x ∈ s, Set.indicator (X ⁻¹' {x}) (fun _ : Ω => x) ω ∂P := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hrepr
      _ = ∑ x ∈ s, ∫ ω, Set.indicator (X ⁻¹' {x}) (fun _ : Ω => x) ω ∂P := by
        exact MeasureTheory.integral_finset_sum s hterm_integrable
      _ = ∑ x ∈ s, x * P.real (X ⁻¹' {x}) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [show Set.indicator (X ⁻¹' {x}) (fun _ : Ω => x) =
            fun ω => x * Set.indicator (X ⁻¹' {x}) (fun _ : Ω => (1 : ℝ)) ω by
              funext ω
              by_cases hω : ω ∈ X ⁻¹' {x}
              · simp [Set.indicator, hω]
              · simp [Set.indicator, hω]]
        rw [MeasureTheory.integral_const_mul]
        have hOne :
            ∫ a, Set.indicator (X ⁻¹' {x}) (fun _ : Ω => (1 : ℝ)) a ∂P =
              P.real (X ⁻¹' {x}) := by
          simpa using
            (MeasureTheory.integral_indicator_one
              (μ := P) (s := X ⁻¹' {x}) (hs := hXm (measurableSet_singleton x)))
        exact congrArg (fun r : ℝ => x * r) hOne
  have hXmE : Measurable fun ω => (X ω : EReal) := by
    fun_prop
  have hTextbookIntegrable :
      textbookIntegrable P (fun ω => (X ω : EReal)) := by
    exact Thm67Support.textbookIntegrable_realCoe_of_integrable hXm hX_integrable
  refine ⟨hrepr, ?_⟩
  rw [expectation_eq_textbookIntegral]
  rw [Thm67Support.textbookIntegral_eq_some_toRealIntegral
    (μ := P) (X := fun ω => (X ω : EReal)) hXmE hTextbookIntegrable]
  have hIntegralEReal :
      (((∫ ω, X ω ∂P : ℝ)) : EReal) =
        (((∑ x ∈ s, x * P.real (X ⁻¹' {x}) : ℝ)) : EReal) := by
    exact congrArg (fun r : ℝ => ((r : EReal))) hIntegral
  apply congrArg some
  simpa using hIntegralEReal
