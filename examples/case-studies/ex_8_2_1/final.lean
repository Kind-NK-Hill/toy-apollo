import Mathlib

/-!
Sanitized public Interface slice for case study `ex_8_2_1`.
The private source excerpt and prompt-pack metadata are omitted.
-/

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Reviewed real-carrier Poisson marginal, built as a measurable pushforward. -/
noncomputable def reviewedPoissonOnReal (r : NNReal) : Measure ℝ :=
  (poissonMeasure r).map (fun n : ℕ => (n : ℝ))

instance (r : NNReal) : IsProbabilityMeasure (reviewedPoissonOnReal r) := by
  unfold reviewedPoissonOnReal
  exact Measure.isProbabilityMeasure_map Nat.cast_continuous.measurable.aemeasurable

/-- Reviewed product now has the literal `ℝ × ℝ` carrier. -/
noncomputable def reviewedPoissonGaussianProduct (r : NNReal) : Measure (ℝ × ℝ) :=
  (reviewedPoissonOnReal r).prod (gaussianReal (0 : ℝ) (1 : NNReal))

def reviewedPoissonSupport : Set ℝ :=
  Set.range (fun n : ℕ => (n : ℝ))

theorem reviewedPoissonSupportMeasurable :
    MeasurableSet reviewedPoissonSupport :=
  (Set.countable_range (fun n : ℕ => (n : ℝ))).measurableSet

/-- Public rectangle Interface on the reviewed real carrier. -/
theorem reviewedRectangleFormula
    (r : NNReal) (n : ℕ) (a b : ℝ) :
    reviewedPoissonGaussianProduct r
        ({(n : ℝ)} ×ˢ Set.Icc a b) =
      reviewedPoissonOnReal r {(n : ℝ)} *
        gaussianReal (0 : ℝ) (1 : NNReal) (Set.Icc a b) := by
  exact Measure.prod_prod
    (μ := reviewedPoissonOnReal r)
    (ν := gaussianReal (0 : ℝ) (1 : NNReal))
    ({(n : ℝ)} : Set ℝ)
    (Set.Icc a b)
