/-
TASK ID: prob_14_4
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_14.thm_14_1
import ProbabilityTheory.chapter_14.prob_14_3




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section



def prob_14_4_gaussianCharacteristic (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((-((((n : ℝ) + 1)⁻¹) * t ^ 2 / 2)) : ℝ) : ℂ)

 
def prob_14_4_limitDistribution : ProbabilityMeasure ℝ :=
  diracProba (0 : ℝ)

 
def prob_14_4_limitCharacteristic (_t : ℝ) : ℂ :=
  1

 
structure prob_14_4_ShrinkingGaussianSetup where
  gaussianLaws : ℕ → ProbabilityMeasure ℝ
  gaussian_law :
    ∀ n : ℕ,
      prob_14_3_isCenteredGaussianLaw
        (gaussianLaws n) (((n : ℝ) + 1)⁻¹)



theorem prob_14_4_gaussian_characteristic
    (S : prob_14_4_ShrinkingGaussianSetup) (n : ℕ) (t : ℝ) :
    thm_14_1_characteristicFunction (S.gaussianLaws n) t =
      prob_14_4_gaussianCharacteristic n t := by
  simpa [prob_14_4_gaussianCharacteristic] using S.gaussian_law n t

 
theorem prob_14_4_dirac_zero_characteristic (t : ℝ) :
    thm_14_1_characteristicFunction prob_14_4_limitDistribution t =
      prob_14_4_limitCharacteristic t := by
  rw [prob_14_4_limitDistribution, prob_14_4_limitCharacteristic,
    thm_14_1_characteristicFunction]
  change charFun (Measure.dirac (0 : ℝ)) t = (1 : ℂ)
  simp



theorem prob_14_4_gaussian_characteristic_limit
    (S : prob_14_4_ShrinkingGaussianSetup) :
    thm_14_1_pointwiseCharFunConvergence
      S.gaussianLaws prob_14_4_limitCharacteristic := by
  intro t
  have hbase :
      Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)) atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hreal :
      Tendsto (fun n : ℕ => -((((n : ℝ) + 1)⁻¹) * t ^ 2 / 2))
        atTop (𝓝 (0 : ℝ)) := by
    have hscaled :
        Tendsto
          (fun n : ℕ => (-(t ^ 2 / 2)) * (((n : ℝ) + 1)⁻¹))
          atTop (𝓝 ((-(t ^ 2 / 2)) * 0)) := by
      exact tendsto_const_nhds.mul hbase
    convert hscaled using 1
    · ext n
      ring_nf
    · ring_nf
  have hcomplex :
      Tendsto
        (fun n : ℕ =>
          ((-((((n : ℝ) + 1)⁻¹) * t ^ 2 / 2) : ℝ) : ℂ))
        atTop (𝓝 (0 : ℂ)) := by
    change
      Tendsto
        (fun n : ℕ =>
          Complex.ofReal (-((((n : ℝ) + 1)⁻¹) * t ^ 2 / 2)))
        atTop (𝓝 (Complex.ofReal 0))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hexp := hcomplex.cexp
  rw [show prob_14_4_limitCharacteristic t = (1 : ℂ) by rfl]
  convert hexp using 1
  · ext n
    rw [prob_14_4_gaussian_characteristic S n t]
    rfl
  · simp

 
theorem prob_14_4_converges_to_dirac_zero
    (S : prob_14_4_ShrinkingGaussianSetup) :
    Tendsto S.gaussianLaws atTop (𝓝 prob_14_4_limitDistribution) := by
  exact
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun
      (μ := S.gaussianLaws) (μ₀ := prob_14_4_limitDistribution)).2
      (fun t => by
        have h := prob_14_4_gaussian_characteristic_limit S t
        rw [← prob_14_4_dirac_zero_characteristic t] at h
        simpa [thm_14_1_characteristicFunction] using h)



theorem prob_14_4_limit_is_dirac_zero_characteristic :
    thm_14_1_limitIsCharacteristic prob_14_4_limitCharacteristic := by
  refine ⟨prob_14_4_limitDistribution, ?_⟩
  intro t
  exact (prob_14_4_dirac_zero_characteristic t).symm



theorem prob_14_4
    (S : prob_14_4_ShrinkingGaussianSetup) :
    Tendsto S.gaussianLaws atTop (𝓝 prob_14_4_limitDistribution) ∧
      thm_14_1_weakLimit S.gaussianLaws ∧
        thm_14_1_limitIsCharacteristic prob_14_4_limitCharacteristic := by
  have hconv := prob_14_4_converges_to_dirac_zero S
  exact ⟨hconv, ⟨prob_14_4_limitDistribution, hconv⟩,
    prob_14_4_limit_is_dirac_zero_characteristic⟩
