/-
TASK ID: ex_10_5_1
TYPE: Example_Proof
SOURCE PLAN: chapter10-continuous-mapping
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_10_11
import ToyApollo.Output.def_10_1
import ToyApollo.Output.def_10_2

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

theorem ex_10_5_1_strong {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (varianceEstimator : ℕ → Ω → ℝ) (variance : ℝ)
    (hstrong :
      ConvergesAlmostSurely μ varianceEstimator (fun _ : Ω => variance)) :
    ConvergesAlmostSurely μ
      (fun n ω => Real.sqrt (varianceEstimator n ω))
      (fun _ : Ω => Real.sqrt variance) := by
  filter_upwards [hstrong] with ω hω
  exact Real.continuous_sqrt.continuousAt.tendsto.comp hω

theorem ex_10_5_1_weak {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (varianceEstimator : ℕ → Ω → ℝ) (variance : ℝ)
    (hVn_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable (fun ω : Ω => fun _ : Fin 1 => varianceEstimator n ω) μ)
    (hsqrt_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω : Ω => fun _ : Fin 1 => Real.sqrt (varianceEstimator n ω)) μ)
    (hweak :
      ConvergesInProbability μ varianceEstimator (fun _ : Ω => variance)) :
    ConvergesInProbability μ
      (fun n ω => Real.sqrt (varianceEstimator n ω))
      (fun _ : Ω => Real.sqrt variance) := by
  let Vn : ℕ → Ω → Fin 1 → ℝ :=
    fun n ω _ => varianceEstimator n ω
  let V : Ω → Fin 1 → ℝ :=
    fun _ _ => variance
  let sqrtMap : (Fin 1 → ℝ) → (Fin 1 → ℝ) :=
    fun v _ => Real.sqrt (v 0)
  have hvec : VectorConvergesInProbability μ Vn V := by
    apply (thm_10_10_probability_iff μ Vn V).mpr
    intro i
    fin_cases i
    simpa [Vn, V] using hweak
  have hs_cont : ∀ v ∈ (Set.univ : Set (Fin 1 → ℝ)), ContinuousAt sqrtMap v := by
    intro v _hv
    have hcont : Continuous sqrtMap := by
      apply continuous_pi
      intro i
      fin_cases i
      exact Real.continuous_sqrt.comp (continuous_apply 0)
    exact hcont.continuousAt
  have hvec_sqrt :
      VectorConvergesInProbability μ
        (fun n ω => sqrtMap (Vn n ω)) (fun ω => sqrtMap (V ω)) :=
    thm_10_11_probability μ Vn V sqrtMap Set.univ hVn_meas hsqrt_meas
      (by simp) (by simp [MeasureTheory.IsProbabilityMeasure.measure_univ])
      hs_cont hvec
  have hcoord :=
    (thm_10_10_probability_iff μ
      (fun n ω => sqrtMap (Vn n ω)) (fun ω => sqrtMap (V ω))).mp hvec_sqrt 0
  simpa [sqrtMap, Vn, V] using hcoord

theorem ex_10_5_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (varianceEstimator : ℕ → Ω → ℝ) (variance : ℝ)
    (hVn_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable (fun ω : Ω => fun _ : Fin 1 => varianceEstimator n ω) μ)
    (hsqrt_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω : Ω => fun _ : Fin 1 => Real.sqrt (varianceEstimator n ω)) μ) :
    (ConvergesAlmostSurely μ varianceEstimator (fun _ : Ω => variance) →
      ConvergesAlmostSurely μ
        (fun n ω => Real.sqrt (varianceEstimator n ω))
        (fun _ : Ω => Real.sqrt variance)) ∧
    (ConvergesInProbability μ varianceEstimator (fun _ : Ω => variance) →
      ConvergesInProbability μ
        (fun n ω => Real.sqrt (varianceEstimator n ω))
        (fun _ : Ω => Real.sqrt variance)) := by
  constructor
  · exact ex_10_5_1_strong μ varianceEstimator variance
  · exact ex_10_5_1_weak μ varianceEstimator variance hVn_meas hsqrt_meas
