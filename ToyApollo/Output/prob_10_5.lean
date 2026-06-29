/-
TASK ID: prob_10_5
TYPE: Problem
SOURCE PLAN: chapter10-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_2
import ToyApollo.Output.def_10_3
import ToyApollo.Output.thm_7_5
import ToyApollo.Output.thm_10_5

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

open scoped ENNReal

private theorem prob_10_5_tendstoInMeasure_of_convergesInProbability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hProb : ConvergesInProbability μ Xn X) :
    TendstoInMeasure μ Xn atTop X := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hprob_half := hProb (ε / 2) hhalf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprob_half
    (fun _ => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  have hnorm : ε ≤ |Xn n ω - X ω| := by
    simpa [Real.norm_eq_abs] using hω
  have hstrict : ε / 2 < |Xn n ω - X ω| := by linarith
  simpa [deviationEvent] using hstrict

private theorem prob_10_5_unifIntegrable_of_dominated
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (Xn : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hXn : ∀ n : ℕ, AEStronglyMeasurable (Xn n) μ)
    (hY : Integrable Y μ)
    (hDom : ∀ n : ℕ, ∀ᵐ ω ∂μ, |Xn n ω| ≤ Y ω) :
    UnifIntegrable Xn (1 : ENNReal) μ := by
  refine unifIntegrable_of (p := (1 : ENNReal)) le_rfl ENNReal.one_ne_top hXn ?_
  intro ε hε
  have hYMemLp : MemLp Y (1 : ENNReal) μ :=
    memLp_one_iff_integrable.mpr hY
  have hYUniform : UniformIntegrable (fun _ : Unit => Y) (1 : ENNReal) μ :=
    uniformIntegrable_const le_rfl ENNReal.one_ne_top hYMemLp
  obtain ⟨C, hC⟩ := hYUniform.spec (by norm_num) ENNReal.one_ne_top hε
  refine ⟨C, fun n => ?_⟩
  refine (eLpNorm_mono_ae ?_).trans (hC ())
  filter_upwards [hDom n] with ω hω
  by_cases hx : C ≤ ‖Xn n ω‖₊
  · have hx_mem : ω ∈ {x | C ≤ ‖Xn n x‖₊} := hx
    rw [Set.indicator_of_mem hx_mem]
    have hY_nonneg : 0 ≤ Y ω :=
      le_trans (abs_nonneg (Xn n ω)) hω
    have hx_real : (C : ℝ) ≤ |Xn n ω| := by
      exact_mod_cast hx
    have hCY_abs : (C : ℝ) ≤ |Y ω| := by
      exact hx_real.trans (hω.trans_eq (abs_of_nonneg hY_nonneg).symm)
    have hy : C ≤ ‖Y ω‖₊ := by
      exact_mod_cast hCY_abs
    have hy_mem : ω ∈ {x | C ≤ ‖Y x‖₊} := hy
    rw [Set.indicator_of_mem hy_mem]
    simpa [Real.norm_eq_abs, abs_of_nonneg hY_nonneg] using hω
  · have hx_not_mem : ω ∉ {x | C ≤ ‖Xn n x‖₊} := hx
    rw [Set.indicator_of_notMem hx_not_mem]
    simpa using norm_nonneg ({x | C ≤ ‖Y x‖₊}.indicator Y ω)

theorem prob_10_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hXn : ∀ n : ℕ, AEStronglyMeasurable (Xn n) μ)
    (hProb : ConvergesInProbability μ Xn (fun _ => 0))
    (hY : Integrable Y μ)
    (hDom : ∀ n : ℕ, ∀ᵐ ω ∂μ, |Xn n ω| ≤ Y ω) :
    ConvergesInMean μ Xn (fun _ => 0) :=
by
  have hInMeasure : TendstoInMeasure μ Xn atTop (fun _ : Ω => 0) :=
    prob_10_5_tendstoInMeasure_of_convergesInProbability μ Xn (fun _ : Ω => 0) hProb
  have hUI : UnifIntegrable Xn (1 : ENNReal) μ :=
    prob_10_5_unifIntegrable_of_dominated μ Xn Y hXn hY hDom
  have hLp :
      Tendsto (fun n : ℕ => eLpNorm (Xn n - fun _ : Ω => 0) (1 : ENNReal) μ)
        atTop (nhds (0 : ENNReal)) :=
    tendsto_Lp_finite_of_tendstoInMeasure (μ := μ) (p := (1 : ENNReal))
      le_rfl ENNReal.one_ne_top hXn MemLp.zero hUI hInMeasure
  rw [ConvergesInMean, ConvergesInRthMean]
  refine ⟨by norm_num, ?_⟩
  simpa [meanDeviationMoment, eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply,
    Real.enorm_eq_ofReal_abs, pow_one] using hLp
