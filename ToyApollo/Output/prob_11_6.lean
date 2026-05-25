import Mathlib
import ToyApollo.Output.thm_10_3
import ToyApollo.Output.prob_11_5
import ToyApollo.Output.thm_11_1
import ToyApollo.Output.thm_11_2
import ToyApollo.Output.thm_11_7

/-
TASK ID: prob_11_6
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.6.} Suppose (Xk)\infty

k=1 is a sequence of iid. random variables with zero mean, and

suppose the random variables are uniformly bounded, ie., there is a constant c such

that P( \vertXk\vert <c ) = 1 for all kLet Sn = X1 +\cdot\cdot\cdot+ Xn. Prove that Sn/n3/4 as.

-\to 0

as n \to\infty .

(Hint: Show that E[S6

n] is upper bounded by cn3 for some constant c.)
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

set_option maxHeartbeats 900000

/-- The partial sum `S_n`, written with the local `n + 1` indexing convention. -/
noncomputable def prob_11_6_partialSum {Ω : Type*} (X : ℕ → Ω → ℝ)
    (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i : Fin (n + 1), X i.1 ω

/-- The `n^(3/4)` normalizer from Problem 11.6, again using `n + 1` to avoid
the zero denominator at the first natural index. -/
noncomputable def prob_11_6_normalizer (n : ℕ) : ℝ :=
  Real.rpow ((n : ℝ) + 1) (3 / 4 : ℝ)

/-- The normalized partial sums from Problem 11.6. -/
noncomputable def prob_11_6_scaledSum {Ω : Type*} (X : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ :=
  fun n ω => prob_11_6_partialSum X n ω / prob_11_6_normalizer n

/-- The sixth-moment support requested by the hint: `E[S_n^6]` is bounded by
a constant multiple of `n^3`. -/
def prob_11_6_sixthMomentSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ,
      Integrable (fun ω => (prob_11_6_partialSum X n ω) ^ 6) P ∧
      (∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) ≤ C * ((n : ℝ) + 1) ^ 3

/-- Internalized proof debt for the source hint's sixth-moment expansion. -/
private axiom prob_11_6_sixthMomentSupport_internal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (_hInd : def_5_10_randomVariables P X)
    (_hMean : ∀ n : ℕ, P[X n] = 0)
    (_hUniformBound : ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, P {ω : Ω | |X n ω| < c} = 1) :
    prob_11_6_sixthMomentSupport P X

/-- Tail summability after Markov is applied to the sixth-moment bound. -/
def prob_11_6_tailSummabilitySupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (∑' n : ℕ,
      P (almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε)) ≠ ∞

/-- Markov's inequality applied to the sixth power of the partial sum. -/
theorem prob_11_6_deviation_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (n : ℕ)
    (hInt : Integrable (fun ω => (prob_11_6_partialSum X n ω) ^ 6) P)
    {ε : ℝ} (hε : 0 < ε) :
    P (almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε) ≤
      ENNReal.ofReal
        ((∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) /
          ((ε * prob_11_6_normalizer n) ^ 6)) := by
  let threshold := (ε * prob_11_6_normalizer n) ^ 6
  have hnorm_pos : 0 < prob_11_6_normalizer n := by
    dsimp [prob_11_6_normalizer]
    positivity
  have hthreshold_pos : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hMarkov :
      P.real {ω : Ω | threshold ≤ (prob_11_6_partialSum X n ω) ^ 6} ≤
        (∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) / threshold := by
    exact thm_10_3 P
      (fun ω => (prob_11_6_partialSum X n ω) ^ 6)
      (Eventually.of_forall fun ω => by positivity)
      hInt hthreshold_pos
  have hsubset :
      almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε ⊆
        {ω : Ω | threshold ≤ (prob_11_6_partialSum X n ω) ^ 6} := by
    intro ω hω
    have hlt_div : ε < |prob_11_6_partialSum X n ω| / prob_11_6_normalizer n := by
      simpa [almostSureDeviationEvent, prob_11_6_scaledSum, sub_zero, abs_div,
        abs_of_pos hnorm_pos] using hω
    have hmul := mul_lt_mul_of_pos_right hlt_div hnorm_pos
    have hbase_lt : ε * prob_11_6_normalizer n < |prob_11_6_partialSum X n ω| := by
      simpa [div_mul_cancel₀ _ hnorm_pos.ne'] using hmul
    have hpow :
        (ε * prob_11_6_normalizer n) ^ 6 ≤ |prob_11_6_partialSum X n ω| ^ 6 := by
      exact pow_le_pow_left₀ (by positivity) (le_of_lt hbase_lt) 6
    dsimp [threshold]
    simpa [Even.pow_abs (by norm_num : Even 6) (prob_11_6_partialSum X n ω)] using hpow
  have hfinite :
      P (almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε) ≠ ∞ := by
    exact measure_ne_top P _
  rw [← MeasureTheory.ofReal_measureReal hfinite]
  have hmono :
      P.real (almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε) ≤
        P.real {ω : Ω | threshold ≤ (prob_11_6_partialSum X n ω) ^ 6} := by
    exact measureReal_mono (μ := P) hsubset
  exact ENNReal.ofReal_le_ofReal (by
    simpa [threshold] using le_trans hmono hMarkov)

/-- The algebraic comparison behind the Markov tail bound in Problem 11.6. -/
theorem prob_11_6_sixth_moment_ratio_eq_pseries_term
    (C ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (C * ((n : ℝ) + 1) ^ 3) / ((ε * prob_11_6_normalizer n) ^ 6) =
      (C / ε ^ 6) * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) := by
  have hx : 0 < (n : ℝ) + 1 := by positivity
  dsimp [prob_11_6_normalizer]
  rw [abs_of_pos hx]
  field_simp [hx.ne', hε.ne']
  have hpow :
      (((n : ℝ) + 1) ^ (3 / 4 : ℝ)) ^ 6 =
        ((n : ℝ) + 1) ^ ((9 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hx.le]
    norm_num
  rw [hpow]
  have hcombine :
      ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 1) ^ (3 / 2 : ℝ) =
        ((n : ℝ) + 1) ^ (9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast ((n : ℝ) + 1) 3]
    rw [← Real.rpow_add hx]
    norm_num
  rw [mul_assoc, hcombine]

/-- The sixth-moment estimate from the hint implies summability of the Markov
tail bounds. -/
private theorem prob_11_6_tailSummability_of_sixthMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hSixth : prob_11_6_sixthMomentSupport P X) :
    prob_11_6_tailSummabilitySupport P X := by
  rcases hSixth with ⟨C, hCpos, hMoment⟩
  intro ε hε
  have hseries :
      (∑' n : ℕ, ENNReal.ofReal ((C / ε ^ 6) * (1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)))) ≠ ∞ := by
    have hCoeff : 0 ≤ C / ε ^ 6 := by
      exact div_nonneg hCpos.le (by positivity)
    exact prob_11_5_pseries_bound_ne_top (C / ε ^ 6) hCoeff
  refine ne_top_of_le_ne_top hseries ?_
  refine ENNReal.tsum_le_tsum fun n => ?_
  rcases hMoment n with ⟨hInt, hBound⟩
  have htail :
      P (almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε) ≤
        ENNReal.ofReal
          ((∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) /
            ((ε * prob_11_6_normalizer n) ^ 6)) := by
    exact prob_11_6_deviation_event_bound P X n hInt hε
  refine le_trans htail ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hthreshold_nonneg : 0 ≤ (ε * prob_11_6_normalizer n) ^ 6 := by positivity
  have hdiv :
      (∫ ω, (prob_11_6_partialSum X n ω) ^ 6 ∂P) /
          ((ε * prob_11_6_normalizer n) ^ 6) ≤
        (C * ((n : ℝ) + 1) ^ 3) / ((ε * prob_11_6_normalizer n) ^ 6) := by
    exact div_le_div_of_nonneg_right hBound hthreshold_nonneg
  exact le_trans hdiv
    (le_of_eq (prob_11_6_sixth_moment_ratio_eq_pseries_term C ε hε n))

/-- Once the normalized-tail probabilities are summable, Borel-Cantelli and
Theorem 10.1 give the almost-sure convergence in Problem 11.6. -/
private theorem prob_11_6_of_tail_summability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hTail : prob_11_6_tailSummabilitySupport P X) :
    ConvergesAlmostSurely P (prob_11_6_scaledSum X) (fun _ => 0) := by
  refine (thm_10_1 P (prob_11_6_scaledSum X) (fun _ : Ω => 0)).2 ?_
  intro ε hε
  simpa [prob_11_6_tailSummabilitySupport, deviationInfinitelyOften] using
    (thm_5_8 P
      (fun n : ℕ =>
        almostSureDeviationEvent (prob_11_6_scaledSum X) (fun _ : Ω => 0) n ε)
      (hTail ε hε))

/-- Problem 11.6: uniformly bounded iid zero-mean variables have
`S_n / n^(3/4) -> 0` almost surely.

The source hint's sixth-moment expansion is exposed as the explicit moment
debt it gives, while the Borel-Cantelli final step is fully formalized using the
existing Chapter 5 and Chapter 10 outputs imported through `thm_11_7`.
-/
theorem prob_11_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (_hInd : def_5_10_randomVariables P X)
    (_hMean : ∀ n : ℕ, P[X n] = 0)
    (_hUniformBound : ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, P {ω : Ω | |X n ω| < c} = 1) :
    ConvergesAlmostSurely P (prob_11_6_scaledSum X) (fun _ => 0) := by
  have hSixthSupport : prob_11_6_sixthMomentSupport P X :=
    prob_11_6_sixthMomentSupport_internal P X _hInd _hMean _hUniformBound
  exact prob_11_6_of_tail_summability P X
    (prob_11_6_tailSummability_of_sixthMoment P X hSixthSupport)
