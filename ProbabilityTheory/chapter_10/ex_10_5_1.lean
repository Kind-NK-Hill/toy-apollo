/-
TASK ID: ex_10_5_1
TYPE: Example_Proof
SOURCE PLAN: chapter10-continuous-mapping
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.thm_10_11
import ProbabilityTheory.chapter_10.def_10_1
import ProbabilityTheory.chapter_10.def_10_2




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
  rcases hstrong with ⟨hEstimator, hVariance, hstrong⟩
  refine ⟨fun n => Real.continuous_sqrt.comp_aestronglyMeasurable (hEstimator n),
    Real.continuous_sqrt.comp_aestronglyMeasurable hVariance, ?_⟩
  filter_upwards [hstrong] with ω hω
  exact Real.continuous_sqrt.continuousAt.tendsto.comp hω



theorem ex_10_5_1_weak {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (varianceEstimator : ℕ → Ω → ℝ) (variance : ℝ)
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
  have hVn_meas : ∀ n : ℕ, AEStronglyMeasurable (Vn n) μ := by
    intro n
    apply Measurable.aestronglyMeasurable
    rw [measurable_pi_iff]
    intro i
    fin_cases i
    simpa [Vn] using hweak.1 n
  have hVn_coord_meas :
      ∀ n : ℕ, ∀ i : Fin 1, Measurable (fun ω => Vn n ω i) := by
    intro n i
    fin_cases i
    simpa [Vn] using hweak.1 n
  have hV_coord_meas :
      ∀ i : Fin 1, Measurable (fun ω => V ω i) := by
    intro i
    fin_cases i
    simpa [V] using hweak.2.1
  have hvec : VectorConvergesInProbability μ Vn V := by
    apply (thm_10_10_probability_iff μ Vn V hVn_coord_meas hV_coord_meas).mpr
    intro i
    fin_cases i
    simpa [Vn, V] using hweak
  have hsqrtMap_cont : Continuous sqrtMap := by
    apply continuous_pi
    intro i
    fin_cases i
    exact Real.continuous_sqrt.comp (continuous_apply 0)
  have hs_cont : ∀ v ∈ (Set.univ : Set (Fin 1 → ℝ)), ContinuousAt sqrtMap v := by
    exact fun v _hv => hsqrtMap_cont.continuousAt
  have hvec_sqrt :
      VectorConvergesInProbability μ
        (fun n ω => sqrtMap (Vn n ω)) (fun ω => sqrtMap (V ω)) :=
    thm_10_11_probability μ Vn V sqrtMap Set.univ hVn_meas
      (by simp) (by simp [MeasureTheory.IsProbabilityMeasure.measure_univ])
      hs_cont hvec
  have hsqrtVn_coord_meas :
      ∀ n : ℕ, ∀ i : Fin 1,
        Measurable (fun ω => sqrtMap (Vn n ω) i) := by
    intro n i
    fin_cases i
    simpa [sqrtMap, Vn, Function.comp_def] using
      Real.continuous_sqrt.measurable.comp (hweak.1 n)
  have hsqrtV_coord_meas :
      ∀ i : Fin 1, Measurable (fun ω => sqrtMap (V ω) i) := by
    intro i
    fin_cases i
    simpa [sqrtMap, V, Function.comp_apply] using
      Real.continuous_sqrt.measurable.comp hweak.2.1
  have hcoord :=
    (thm_10_10_probability_iff μ
      (fun n ω => sqrtMap (Vn n ω)) (fun ω => sqrtMap (V ω))
      hsqrtVn_coord_meas hsqrtV_coord_meas).mp hvec_sqrt 0
  simpa [sqrtMap, Vn, V] using hcoord



theorem ex_10_5_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (varianceEstimator : ℕ → Ω → ℝ) (variance : ℝ) :
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
  · exact ex_10_5_1_weak μ varianceEstimator variance
