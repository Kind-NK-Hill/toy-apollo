import ToyApollo.Output.prob_11_9_probability_support

open Filter MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators

/-- Problem 11.9: in the independent uniform occupancy experiment with
`k_n / n → a > 0`, the proportion of empty boxes converges to `e^{-a}` in
quadratic mean and hence in probability. -/
theorem prob_11_9_support_result {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) ∧
      ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) := by
  let hMS := prob_11_9_quadratic_mean P boxes k X a hModel hRegime hX
  exact ⟨hMS, prob_11_9_probability P boxes X a hMS hX⟩
