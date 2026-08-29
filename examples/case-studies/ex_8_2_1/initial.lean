import Mathlib

/-!
Sanitized public Interface slice for case study `ex_8_2_1`.
The private source excerpt and prompt-pack metadata are omitted.
-/

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Initial compiling object: the discrete marginal keeps its intrinsic `ℕ` carrier. -/
noncomputable def initialPoissonGaussianProduct (r : NNReal) : Measure (ℕ × ℝ) :=
  (poissonMeasure r).prod (gaussianReal (0 : ℝ) (1 : NNReal))

/-- The local rectangle calculation is valid, but it lives on `ℕ × ℝ`. -/
theorem initialRectangleFormula (r : NNReal) (n : ℕ) (a b : ℝ) :
    initialPoissonGaussianProduct r ({n} ×ˢ Set.Icc a b) =
      ENNReal.ofReal
        (poissonPMFReal r n *
          ∫ x in Set.Icc a b, gaussianPDFReal (0 : ℝ) (1 : NNReal) x) := by
  rw [initialPoissonGaussianProduct, Measure.prod_prod]
  rw [poissonMeasure_singleton]
  rw [gaussianReal_apply_eq_integral
    (μ := (0 : ℝ)) (v := (1 : NNReal)) (hv := by norm_num)]
  change ENNReal.ofReal (poissonPMFReal r n) * _ = _
  rw [← ENNReal.ofReal_mul (poissonPMFReal_nonneg)]
