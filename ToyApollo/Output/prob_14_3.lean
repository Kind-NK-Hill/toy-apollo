/-
TASK ID: prob_14_3
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_14_1

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

def prob_14_3_gaussianCharacteristic (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((-(((n : ℝ) + 1) * t ^ 2 / 2)) : ℝ) : ℂ)

def prob_14_3_isCenteredGaussianLaw
    (P : ProbabilityMeasure ℝ) (variance : ℝ) : Prop :=
  ∀ t : ℝ,
    thm_14_1_characteristicFunction P t =
      Complex.exp (((-(variance * t ^ 2 / 2)) : ℝ) : ℂ)

def prob_14_3_limitCharacteristic (t : ℝ) : ℂ :=
  if t = 0 then 1 else 0

structure prob_14_3_GaussianVarianceEscapeSetup where
  gaussianLaws : ℕ → ProbabilityMeasure ℝ
  gaussian_law :
    ∀ n : ℕ,
      prob_14_3_isCenteredGaussianLaw (gaussianLaws n) ((n : ℝ) + 1)
  tight_to_weak_by_levy :
    thm_14_1_tight gaussianLaws → thm_14_1_weakLimit gaussianLaws

theorem prob_14_3_gaussian_characteristic
    (S : prob_14_3_GaussianVarianceEscapeSetup) (n : ℕ) (t : ℝ) :
    thm_14_1_characteristicFunction (S.gaussianLaws n) t =
      prob_14_3_gaussianCharacteristic n t := by
  simpa [prob_14_3_gaussianCharacteristic] using S.gaussian_law n t

theorem prob_14_3_gaussian_characteristic_limit
    (S : prob_14_3_GaussianVarianceEscapeSetup) :
    thm_14_1_pointwiseCharFunConvergence
      S.gaussianLaws prob_14_3_limitCharacteristic := by
  intro t
  by_cases ht : t = 0
  · have hconst :
        (fun n : ℕ => thm_14_1_characteristicFunction (S.gaussianLaws n) t) =
          fun _ : ℕ => (1 : ℂ) := by
      funext n
      rw [prob_14_3_gaussian_characteristic S n t, prob_14_3_gaussianCharacteristic, ht]
      simp
    rw [hconst, prob_14_3_limitCharacteristic, if_pos ht]
    exact tendsto_const_nhds
  · have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    have hcoef_neg : -(t ^ 2 / 2) < 0 := by
      have ht_sq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
      have hhalf : 0 < t ^ 2 / 2 := by positivity
      linarith
    have harg0 :
        Tendsto (fun n : ℕ => (-(t ^ 2 / 2)) * (((n : ℝ) + 1))) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg hcoef_neg hbase
    have harg :
        Tendsto (fun n : ℕ => -((((n : ℝ) + 1) * t ^ 2 / 2))) atTop atBot := by
      convert harg0 using 1
      ext n
      ring
    have hreal :
        Tendsto (fun n : ℕ => Real.exp (-((((n : ℝ) + 1) * t ^ 2 / 2)))) atTop
          (𝓝 0) :=
      Real.tendsto_exp_atBot.comp harg
    have hcomplex :
        Tendsto
          (fun n : ℕ =>
            ((Real.exp (-((((n : ℝ) + 1) * t ^ 2 / 2))) : ℝ) : ℂ))
          atTop (𝓝 (0 : ℂ)) := by
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    have htarget : prob_14_3_limitCharacteristic t = (0 : ℂ) := by
      simp [prob_14_3_limitCharacteristic, ht]
    rw [htarget]
    convert hcomplex using 1
    ext n
    rw [prob_14_3_gaussian_characteristic S n t, prob_14_3_gaussianCharacteristic]
    rw [← Complex.ofReal_exp]

theorem prob_14_3_limitCharacteristic_not_continuousAtZero :
    ¬ thm_14_1_continuousAtZero prob_14_3_limitCharacteristic := by
  intro h
  have hcont :
      ContinuousAt prob_14_3_limitCharacteristic (0 : ℝ) := by
    simpa [thm_14_1_continuousAtZero] using h
  have hseq :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcomp :
      Tendsto
        (fun n : ℕ =>
          prob_14_3_limitCharacteristic ((1 : ℝ) / ((n : ℝ) + 1)))
        atTop (𝓝 (prob_14_3_limitCharacteristic 0)) := by
    exact hcont.tendsto.comp hseq
  have hbad :
      Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    convert hcomp using 1
    · funext n
      have hden_pos : 0 < ((n : ℝ) + 1) := by positivity
      have hden : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hden_pos
      have hn : (1 : ℝ) / ((n : ℝ) + 1) ≠ 0 := by
        exact div_ne_zero one_ne_zero hden
      rw [prob_14_3_limitCharacteristic, if_neg hn]
    · simp [prob_14_3_limitCharacteristic]
  have hzero :
      Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (0 : ℂ)) :=
    tendsto_const_nhds
  have h01 : (1 : ℂ) = 0 := tendsto_nhds_unique hbad hzero
  norm_num at h01

theorem prob_14_3_limitCharacteristic_not_characteristic :
    ¬ thm_14_1_limitIsCharacteristic prob_14_3_limitCharacteristic := by
  intro hchar
  exact prob_14_3_limitCharacteristic_not_continuousAtZero
    (thm_14_1_characteristic_continuousAtZero hchar)

theorem prob_14_3_not_weakLimit
    (S : prob_14_3_GaussianVarianceEscapeSetup) :
    ¬ thm_14_1_weakLimit S.gaussianLaws := by
  intro hweak
  exact prob_14_3_limitCharacteristic_not_characteristic
    ((thm_14_1_weak_iff_characteristic
      (prob_14_3_gaussian_characteristic_limit S)).mp hweak)

theorem prob_14_3_not_tight
    (S : prob_14_3_GaussianVarianceEscapeSetup) :
    ¬ thm_14_1_tight S.gaussianLaws := by
  intro htight
  exact prob_14_3_not_weakLimit S (S.tight_to_weak_by_levy htight)

theorem prob_14_3
    (S : prob_14_3_GaussianVarianceEscapeSetup) :
    (¬ thm_14_1_weakLimit S.gaussianLaws) ∧
      (¬ thm_14_1_limitIsCharacteristic prob_14_3_limitCharacteristic) ∧
        (¬ thm_14_1_continuousAtZero prob_14_3_limitCharacteristic) ∧
          (¬ thm_14_1_tight S.gaussianLaws) := by
  exact ⟨prob_14_3_not_weakLimit S,
    prob_14_3_limitCharacteristic_not_characteristic,
    prob_14_3_limitCharacteristic_not_continuousAtZero,
    prob_14_3_not_tight S⟩
