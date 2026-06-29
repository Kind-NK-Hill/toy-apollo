import Mathlib

open MeasureTheory MeasureTheory.Measure Set Filter

/-
TASK ID: prob_7_4
TYPE: Problem
SOURCE PLAN: 30_chap7_problems
TASK CONTENT:
\textbf{7.4.} Let $X$ be an integrable function on a measure space $(\Omega,\mathcal{F},\mu)$. Show that for any $\epsilon$, there exists a set $E\in \mathcal{F}$ with $\mu(E)<\infty$ such that
\[
\left|\int_{E^c} X\, d\mu\right|<\epsilon.
\]
-/

/-- Problem 7.4: an integrable function has small integral outside a
finite-measure measurable set. -/
theorem prob_7_4 {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ)
    (hX : Integrable X μ) :
    ∀ ε > 0, ∃ E : Set Ω, MeasurableSet E ∧ μ E < ⊤ ∧ |∫ ω in Eᶜ, X ω ∂μ| < ε := by
  revert hX
  intro hX_integrable
  set E : ℕ → Set Ω := fun n => {ω | abs (X ω) > 1 / (n + 1)} with hE_def
  have h_int_Ec :
      Filter.Tendsto
        (fun n => ∫ ω in (MeasureTheory.toMeasurable μ (E n))ᶜ, abs (X ω) ∂μ)
        Filter.atTop (nhds 0) := by
    have h_int_Ec :
        Filter.Tendsto
          (fun n =>
            ∫ ω, (1 - (Set.indicator (MeasureTheory.toMeasurable μ (E n)) 1) ω) *
              abs (X ω) ∂μ)
          Filter.atTop (nhds 0) := by
      have h_int_Ec :
          ∀ᵐ ω ∂μ,
            Filter.Tendsto
              (fun n =>
                (1 - (Set.indicator (MeasureTheory.toMeasurable μ (E n)) 1) ω) *
                  abs (X ω))
              Filter.atTop (nhds 0) := by
        filter_upwards [] with ω
        by_cases hω : X ω = 0 <;> simp_all +decide [Set.indicator]
        refine' tendsto_const_nhds.congr' _
        filter_upwards [Filter.eventually_gt_atTop ⌈|X ω|⁻¹⌉₊] with n hn
        split_ifs <;> simp_all +decide
        exact False.elim <|
          ‹ω ∉ toMeasurable μ {ω | ((n + 1 : ℝ)⁻¹ < |X ω|)}› <|
            subset_toMeasurable _ _ <|
              show ((n + 1 : ℝ)⁻¹ < |X ω|) from
                inv_lt_of_inv_lt₀ (abs_pos.mpr hω) <| by
                  linarith [Nat.lt_of_ceil_lt hn]
      convert MeasureTheory.tendsto_integral_of_dominated_convergence _ _ _ _ h_int_Ec
      any_goals exact hX_integrable.norm
      · norm_num
      · intro n
        exact
          MeasureTheory.AEStronglyMeasurable.mul
            (MeasureTheory.AEStronglyMeasurable.sub
              (MeasureTheory.aestronglyMeasurable_const)
              (MeasureTheory.aestronglyMeasurable_const.indicator
                (MeasureTheory.measurableSet_toMeasurable _ _)))
            (hX_integrable.abs.aestronglyMeasurable)
      · intro n
        filter_upwards [] with ω
        by_cases hω : ω ∈ toMeasurable μ (E n) <;> simp +decide [hω]
    convert h_int_Ec using 2
    rw [← MeasureTheory.integral_indicator] <;> norm_num [Set.indicator]
    grind
  intro ε hε_pos
  obtain ⟨N, hN⟩ :
      ∃ N : ℕ,
        ∀ n ≥ N, ∫ ω in (MeasureTheory.toMeasurable μ (E n))ᶜ, abs (X ω) ∂μ < ε := by
    simpa using h_int_Ec.eventually (gt_mem_nhds hε_pos)
  refine' ⟨MeasureTheory.toMeasurable μ (E N), MeasureTheory.measurableSet_toMeasurable _ _, ?_, ?_⟩
  · have h_finite : μ (E N) < ⊤ := by
      have :=
        hX_integrable.measure_norm_ge_lt_top
          (show (1 / (N + 1) : ℝ) > 0 by positivity)
      exact lt_of_le_of_lt (MeasureTheory.measure_mono (fun _ hx => hx.out.le)) this
    rwa [MeasureTheory.measure_toMeasurable]
  · refine' lt_of_le_of_lt (MeasureTheory.norm_integral_le_integral_norm X) (hN N le_rfl)
