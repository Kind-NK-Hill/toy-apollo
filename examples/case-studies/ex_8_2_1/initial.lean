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
      poissonMeasure r {n} *
        gaussianReal (0 : ℝ) (1 : NNReal) (Set.Icc a b) := by
  exact Measure.prod_prod
    (μ := poissonMeasure r)
    (ν := gaussianReal (0 : ℝ) (1 : NNReal))
    ({n} : Set ℕ)
    (Set.Icc a b)
