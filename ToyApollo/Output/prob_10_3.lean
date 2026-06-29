/-
TASK ID: prob_10_3
TYPE: Problem
SOURCE PLAN: chapter10-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_2
import ToyApollo.Output.def_10_4
import ToyApollo.Output.thm_10_7
import ToyApollo.Output.thm_14_2

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

theorem prob_10_3_of_randomVariablesConvergeInDistribution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hXn_meas : ∀ n : ℕ, Measurable (Xn n))
    (hX_meas : Measurable X)
    (hDist : RandomVariablesConvergeInDistribution μ Xn X) :
    TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ := by
  let Pseq : ℕ → ProbabilityMeasure ℝ := def_14_1_laws μ Xn hXn_meas
  let P : ProbabilityMeasure ℝ := def_14_1_law μ X hX_meas
  have hDist' : thm_14_2_cdfConvergence μ Xn X := by
    simpa [RandomVariablesConvergeInDistribution, thm_14_2_cdfConvergence,
      thm_14_2_randomVariableCdf, measureCdf] using hDist
  have hWeak : thm_14_2_weakConvergence μ Xn X hXn_meas hX_meas :=
    thm_14_2_distribution_to_weak μ hXn_meas hX_meas hDist'
  have hLawWeak : def_14_1 Pseq P := by
    simpa [Pseq, P, thm_14_2_weakConvergence, def_14_2, def_14_1,
      def_14_1_randomVariableWeakConvergence, def_14_1_laws, def_14_1_law] using hWeak
  have hTend : Tendsto Pseq atTop (𝓝 P) :=
    (def_14_1_iff_tendsto).1 hLawWeak
  refine ⟨fun n => (hXn_meas n).aemeasurable, hX_meas.aemeasurable, ?_⟩
  simpa [Pseq, P, def_14_1_laws, def_14_1_law] using hTend

theorem prob_10_3_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ)
    (X : Ω → ℝ) (c : ℝ)
    (hX_meas : Measurable X)
    (hDist : TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ)
    (hConst : μ {ω : Ω | X ω = c} = 1) :
    TendstoInMeasure μ Xn atTop X := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let F : Set ℝ := {x : ℝ | ε ≤ ‖x - c‖}
  have hF_closed : IsClosed F := by
    exact isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
  have hX_eq_meas : MeasurableSet {ω : Ω | X ω = c} := by
    change MeasurableSet (X ⁻¹' ({c} : Set ℝ))
    exact hX_meas (measurableSet_singleton c)
  have hX_ne_zero : μ {ω : Ω | X ω ≠ c} = 0 := by
    have hcompl : μ ({ω : Ω | X ω = c})ᶜ = 0 := by
      rw [measure_compl hX_eq_meas (measure_ne_top μ _)]
      simp [hConst, IsProbabilityMeasure.measure_univ (μ := μ)]
    simpa [Set.compl_setOf] using hcompl
  have hlimit_F_zero : (μ.map X) F = 0 := by
    rw [Measure.map_apply hX_meas hF_closed.measurableSet]
    refine measure_mono_null ?_ hX_ne_zero
    intro ω hω hω_eq
    have : ε ≤ ‖X ω - c‖ := hω
    simp [hω_eq, hε.not_ge] at this
  have hlimsup : Filter.limsup (fun n : ℕ => (μ.map (Xn n)) F) atTop ≤ 0 := by
    have hport :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hDist.tendsto hF_closed
    simpa [hlimit_F_zero] using hport
  have htail :
      Tendsto (fun n : ℕ => μ {ω : Ω | ε ≤ ‖Xn n ω - c‖}) atTop (nhds 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    have hev_lt : ∀ᶠ n : ℕ in atTop, (μ.map (Xn n)) F < δ :=
      (Filter.limsup_le_iff).mp hlimsup δ hδ
    filter_upwards [hev_lt] with n hn
    have hmap :=
      Measure.map_apply_of_aemeasurable (hDist.forall_aemeasurable n)
        hF_closed.measurableSet
    have hn' : μ ((Xn n) ⁻¹' F) ≤ δ := by
      rw [← hmap]
      exact hn.le
    simpa [F] using hn'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds htail (fun _ => zero_le _) ?_
  intro n
  calc
    μ {ω : Ω | ε ≤ ‖Xn n ω - X ω‖}
        ≤ μ ({ω : Ω | ε ≤ ‖Xn n ω - c‖} ∪ {ω : Ω | X ω ≠ c}) := by
          apply measure_mono
          intro ω hω
          by_cases hXω : X ω = c
          · left
            simpa [hXω] using hω
          · right
            exact hXω
    _ ≤ μ {ω : Ω | ε ≤ ‖Xn n ω - c‖} + μ {ω : Ω | X ω ≠ c} :=
        measure_union_le _ _
    _ = μ {ω : Ω | ε ≤ ‖Xn n ω - c‖} := by
        simp [hX_ne_zero]

theorem prob_10_3_convergesInProbability_of_tendstoInMeasure {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (h : TendstoInMeasure μ Xn atTop X) :
    ConvergesInProbability μ Xn X := by
  intro ε hε
  have hnorm := (tendstoInMeasure_iff_norm.mp h) ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hnorm (fun _ => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hle : ε ≤ |Xn n ω - X ω| := le_of_lt hω
  simpa [deviationEvent, Real.norm_eq_abs] using hle

theorem prob_10_3_of_tendstoInDistribution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ)
    (X : Ω → ℝ) (c : ℝ)
    (hX_meas : Measurable X)
    (hDist : TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ)
    (hConst : μ {ω : Ω | X ω = c} = 1) :
    ConvergesInProbability μ Xn X :=
  prob_10_3_convergesInProbability_of_tendstoInMeasure μ Xn X
    (prob_10_3_tendstoInMeasure μ Xn X c hX_meas hDist hConst)

theorem prob_10_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (c : ℝ)
    (hX_meas : Measurable X)
    (hXn_meas : ∀ n : ℕ, Measurable (Xn n))
    (hDist : RandomVariablesConvergeInDistribution μ Xn X)
    (hConst : μ {ω : Ω | X ω = c} = 1) :
    ConvergesInProbability μ Xn X :=
  prob_10_3_of_tendstoInDistribution μ Xn X c hX_meas
    (prob_10_3_of_randomVariablesConvergeInDistribution μ Xn X hXn_meas hX_meas hDist)
    hConst
