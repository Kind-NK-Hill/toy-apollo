/-
TASK ID: prob_6_5
TYPE: Problem
SOURCE PLAN: 24_chap6_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem prob_6_5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Integrable X P) :
    ∀ ε > 0, ∃ (f : SimpleFunc Ω ℝ), ∫ ω, |X ω - f ω| ∂P < ε := by
  by_contra! h_contra
  obtain ⟨f_n, hf_n⟩ :
      ∃ f_n : ℕ → SimpleFunc Ω ℝ,
        Filter.Tendsto (fun n => ∫ ω, |X ω - f_n n ω| ∂P) Filter.atTop (nhds 0) := by
    have h_strong := hX.aestronglyMeasurable
    obtain ⟨g, hg⟩ : ∃ g : Ω → ℝ, Measurable g ∧ X =ᵐ[P] g := by
      exact ⟨_, h_strong.measurable_mk, h_strong.ae_eq_mk⟩
    have h_approx := @tendsto_integral_norm_approxOn_sub
    specialize h_approx hg.1 (by exact hX.congr hg.2)
    use fun n => SimpleFunc.approxOn g hg.1 (Set.range g ∪ {0}) 0 (by norm_num) n
    generalize_proofs at *
    convert h_approx using 2
    rw [MeasureTheory.integral_congr_ae]
    filter_upwards [hg.2] with ω hω using by simp +decide [hω, abs_sub_comm]
  exact absurd
    (le_of_tendsto_of_tendsto' tendsto_const_nhds hf_n fun n => h_contra.choose_spec.2 _)
    (by linarith [h_contra.choose_spec.1])
