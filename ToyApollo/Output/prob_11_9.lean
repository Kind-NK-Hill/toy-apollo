import Mathlib
import ToyApollo.Output.def_10_3
import ToyApollo.Output.thm_10_5
import ToyApollo.Output.thm_11_2

/-
TASK ID: prob_11_9
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.9.} Consider the experiment of throwing k distinct balls into n distinct boxes.

Assume the locations of the balls are independent and uniformly chosen among

{1, 2,...,n }We consider an asymptotic scenario in which k and n increase

simultaneously with k/n \to a, for some positive constant aLet Xn denote the

number of empty boxes when the number of boxes is n Prove that X n/n \to e-a in

quadratic mean, and hence in probability as n \to\infty .
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory

noncomputable section

/-- The proportion `X_n / n` of empty boxes, written with an explicit sequence
of box counts so that the Lean indexing need not identify `n = 0` with the
textbook's first positive number of boxes. -/
noncomputable def prob_11_9_emptyBoxRatio {Ω : Type*}
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => X n ω / (boxes n : ℝ)

/-- The asymptotic regime from Problem 11.9: the number of boxes diverges,
`k_n / n` tends to a positive constant `a`, and each experiment has at least
one box. -/
def prob_11_9_asymptoticRegime (boxes k : ℕ → ℕ) (a : ℝ) : Prop :=
  (∀ n : ℕ, 0 < boxes n) ∧
    Tendsto (fun n : ℕ => (boxes n : ℝ)) atTop atTop ∧
    0 < a ∧
    Tendsto (fun n : ℕ => (k n : ℝ) / (boxes n : ℝ)) atTop (nhds a)

/-- Support for the textbook occupancy calculation.  Expanding
`X_n = ∑_j 1_{box j is empty}` gives
`E[(X_n/n - exp (-a))^2] → 0`; the expansion uses the one-box empty
probability `(1 - 1/n)^k` and the two-box joint probability `(1 - 2/n)^k`. -/
def prob_11_9_occupancyMomentSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ) : Prop :=
  prob_11_9_asymptoticRegime boxes k a →
    Tendsto
      (fun n : ℕ =>
        meanDeviationMoment P (prob_11_9_emptyBoxRatio boxes X)
          (fun _ : Ω => Real.exp (-a)) 2 n)
      atTop (nhds 0)

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
private theorem prob_11_9_quadratic_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hMoment : prob_11_9_occupancyMomentSupport P boxes k X a) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) := by
  refine ⟨by norm_num, ?_⟩
  exact hMoment hRegime

/-- Problem 11.9, probability part: the mean-square convergence is passed to
convergence in probability through the Chapter 10 `L^r` result. -/
private theorem prob_11_9_probability {Ω : Type*} [MeasurableSpace Ω]
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
    (fun _ : Ω => Real.exp (-a)) (p := (2 : ENNReal)) (by norm_num) hX hLimit hLp

/-- Problem 11.9: in the independent uniform occupancy experiment with
`k_n / n → a > 0`, the proportion of empty boxes converges to `e^{-a}` in
quadratic mean and hence in probability. -/
theorem prob_11_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hMoment :
      prob_11_9_asymptoticRegime boxes k a →
        Tendsto
          (fun n : ℕ =>
            meanDeviationMoment P (prob_11_9_emptyBoxRatio boxes X)
              (fun _ : Ω => Real.exp (-a)) 2 n)
          atTop (nhds 0))
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) ∧
      ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) := by
  have hMomentSupport : prob_11_9_occupancyMomentSupport P boxes k X a := by
    simpa [prob_11_9_occupancyMomentSupport] using hMoment
  let hMS := prob_11_9_quadratic_mean P boxes k X a hRegime hMomentSupport
  exact ⟨hMS, prob_11_9_probability P boxes X a hMS hX⟩
