/-
TASK ID: ex_8_2_1
TYPE: Example_Proof
SOURCE PLAN: 32_chap8_product_measure_fubini
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_8_2

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Set

noncomputable section

theorem ex_8_2_1 (r : NNReal) (n : ℕ) (a b : ℝ) :
    ((poissonMeasure r).prod (gaussianReal (0 : ℝ) (1 : NNReal))) ({n} ×ˢ Set.Icc a b) =
      ENNReal.ofReal
        (poissonPMFReal r n * ∫ x in Set.Icc a b, gaussianPDFReal (0 : ℝ) (1 : NNReal) x) := by
  have hprod :
      ((poissonMeasure r).prod (gaussianReal (0 : ℝ) (1 : NNReal))) ({n} ×ˢ Set.Icc a b) =
        (poissonMeasure r) {n} * (gaussianReal (0 : ℝ) (1 : NNReal)) (Set.Icc a b) := by
    simpa using
      (Measure.prod_prod
        (μ := poissonMeasure r)
        (ν := gaussianReal (0 : ℝ) (1 : NNReal))
        ({n} : Set ℕ)
        (Set.Icc a b))
  rw [hprod]
  unfold poissonMeasure
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]
  rw [gaussianReal_apply_eq_integral (μ := (0 : ℝ)) (v := (1 : NNReal)) (hv := by norm_num)]
  rw [← poissonPMFReal_ofReal_eq_poissonPMF]
  rw [← ENNReal.ofReal_mul (poissonPMFReal_nonneg)]
