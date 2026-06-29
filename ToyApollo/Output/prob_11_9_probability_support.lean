import ToyApollo.Output.prob_11_9_limit_support

open Filter MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators

/-- Support for translating the concrete mean-square moment statement above to
the `eLpNorm` premise used by Theorem 10.5. -/
def prob_11_9_meanSquareELpNormSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ) : Prop :=
  ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) →
    (∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) ∧
      AEStronglyMeasurable (fun _ : Ω => Real.exp (-a)) P ∧
      Tendsto
        (fun n : ℕ =>
          eLpNorm
            (((prob_11_9_emptyBoxRatio boxes X) n) - fun _ : Ω => Real.exp (-a))
            (2 : ENNReal) P)
        atTop (nhds 0)

/-- The `ConvergesInMeanSquare` definition is exactly the square of the
`L^2` seminorm, so convergence in mean square gives the `eLpNorm` limit needed
by Theorem 10.5. -/
theorem prob_11_9_eLpNorm_tendsto_of_convergesInMeanSquare
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hMS : ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a))) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (((prob_11_9_emptyBoxRatio boxes X) n) -
            fun _ : Ω => Real.exp (-a))
          (2 : ENNReal) P)
      atTop (nhds 0) := by
  rcases hMS with ⟨_hTwo, hTendsto⟩
  have hroot :
      Tendsto (fun y : ENNReal => y ^ (1 / (2 : ℝ))) (nhds 0) (nhds 0) := by
    simpa using
      (ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ)))).tendsto 0
  have hcomp := hroot.comp hTendsto
  convert hcomp using 1
  ext n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  congr with ω
  rw [Real.enorm_eq_ofReal_abs]
  norm_num
  rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]

/-- The remaining bridge from quadratic mean to the Chapter 10 `L^2` interface
is measurable-data only; the analytic norm limit is proved above. -/
theorem prob_11_9_meanSquareELpNormSupport_of_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    prob_11_9_meanSquareELpNormSupport P boxes X a := by
  intro hMS
  exact ⟨hX, aestronglyMeasurable_const,
    prob_11_9_eLpNorm_tendsto_of_convergesInMeanSquare P boxes X a hMS⟩

/-- Problem 11.9, quadratic-mean part: the empty-box proportion converges to
`e^{-a}` in mean square. -/
theorem prob_11_9_quadratic_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) := by
  refine ⟨by norm_num, ?_⟩
  exact
    prob_11_9_occupancy_moment_calculation_internal P boxes k X a hModel
      hRegime hX

/-- Problem 11.9, probability part: the mean-square convergence is passed to
convergence in probability through the Chapter 10 `L^r` result. -/
theorem prob_11_9_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hMS : ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)))
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) := by
  let hELp := prob_11_9_meanSquareELpNormSupport_of_measurable P boxes X a hX
  rcases hELp hMS with ⟨hX, hLimit, hLp⟩
  exact thm_10_5 P (prob_11_9_emptyBoxRatio boxes X)
    (fun _ : Ω => Real.exp (-a)) hX hLimit hMS

/-- Public landing for the "hence in probability" clause of Problem 11.9. -/
theorem prob_11_9_hence_in_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hMS : ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)))
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) :=
  prob_11_9_probability P boxes X a hMS hX
