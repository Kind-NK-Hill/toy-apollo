/-
TASK ID: prob_10_10
TYPE: Problem
SOURCE PLAN: chapter10-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.prob_10_3
import ProbabilityTheory.chapter_10.thm_10_7
import ProbabilityTheory.chapter_10.thm_10_12
import ProbabilityTheory.chapter_10.def_10_4




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section

 
theorem prob_10_10_add_distribution_stability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn Yn : ℕ → Ω → ℝ) (X : Ω → ℝ) (c : ℝ)
    (hX_dist : TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ)
    (hY_prob : TendstoInMeasure μ Yn atTop (fun _ : Ω => c))
    (hY_meas : ∀ n : ℕ, AEMeasurable (Yn n) μ) :
    TendstoInDistribution (fun n ω => Xn n ω + Yn n ω) atTop
      (fun ω => X ω + c) (fun _ : ℕ => μ) μ :=
  hX_dist.add_of_tendstoInMeasure_const hY_prob hY_meas

 
theorem prob_10_10_mul_distribution_stability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn Yn : ℕ → Ω → ℝ) (X : Ω → ℝ) (c : ℝ)
    (hX_dist : TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ)
    (hY_prob : TendstoInMeasure μ Yn atTop (fun _ : Ω => c))
    (hY_meas : ∀ n : ℕ, AEMeasurable (Yn n) μ) :
    TendstoInDistribution (fun n ω => Xn n ω * Yn n ω) atTop
      (fun ω => c * X ω) (fun _ : ℕ => μ) μ := by
  have h :=
    hX_dist.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) hY_prob hY_meas
  simpa [mul_comm] using h



theorem prob_10_10_of_tendstoInDistribution {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn Yn : ℕ → Ω → ℝ) (X : Ω → ℝ) (c : ℝ)
    (hYn_meas : ∀ n : ℕ, Measurable (Yn n))
    (hX_dist : TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ)
    (hY_dist :
      TendstoInDistribution Yn atTop (fun _ : Ω => c) (fun _ : ℕ => μ) μ) :
    TendstoInDistribution (fun n ω => Xn n ω + Yn n ω) atTop
        (fun ω => X ω + c) (fun _ : ℕ => μ) μ ∧
      TendstoInDistribution (fun n ω => Xn n ω * Yn n ω) atTop
        (fun ω => c * X ω) (fun _ : ℕ => μ) μ := by
  have h_const : μ {ω : Ω | (fun _ : Ω => c) ω = c} = 1 := by
    simp [IsProbabilityMeasure.measure_univ (μ := μ)]
  have hY_prob_local : ConvergesInProbability μ Yn (fun _ : Ω => c) :=
    prob_10_3_of_tendstoInDistribution μ Yn (fun _ : Ω => c) c
      hYn_meas (by fun_prop) hY_dist h_const
  have hY_prob : TendstoInMeasure μ Yn atTop (fun _ : Ω => c) :=
    tendstoInMeasure_of_convergesInProbability μ Yn (fun _ : Ω => c) hY_prob_local
  exact ⟨
    prob_10_10_add_distribution_stability μ Xn Yn X c hX_dist hY_prob
      hY_dist.forall_aemeasurable,
    prob_10_10_mul_distribution_stability μ Xn Yn X c hX_dist hY_prob
      hY_dist.forall_aemeasurable⟩



theorem prob_10_10 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn Yn : ℕ → Ω → ℝ) (X : Ω → ℝ) (c : ℝ)
    (hYn_meas : ∀ n : ℕ, Measurable (Yn n))
    (hX_dist : TendstoInDistribution Xn atTop X (fun _ : ℕ => μ) μ)
    (hY_dist :
      TendstoInDistribution Yn atTop (fun _ : Ω => c) (fun _ : ℕ => μ) μ) :
    TendstoInDistribution (fun n ω => Xn n ω + Yn n ω) atTop
        (fun ω => X ω + c) (fun _ : ℕ => μ) μ ∧
      TendstoInDistribution (fun n ω => Xn n ω * Yn n ω) atTop
        (fun ω => c * X ω) (fun _ : ℕ => μ) μ :=
  prob_10_10_of_tendstoInDistribution μ Xn Yn X c hYn_meas hX_dist hY_dist
