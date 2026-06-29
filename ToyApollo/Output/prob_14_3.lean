import Mathlib
import ToyApollo.Output.thm_14_1

/-
TASK ID: prob_14_3
TYPE: Problem
SOURCE PLAN: chapter14-problems
TASK CONTENT:
\textbf{14.3.} Let Xn be the random variable distributed according to the Gaussian distribu-

tion N( 0,n ),f o r n = 1, 2,3,... Show that this sequence of random variables fails

to satisfy all four conditions in Levy's continuity theorem.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

/-- The characteristic function of the textbook law `N(0, n + 1)`.

The book indexes the sequence by `n ≥ 1`; the Lean sequence is indexed by
`ℕ`, so the `n`th Lean term corresponds to variance `n + 1`. -/
def prob_14_3_gaussianCharacteristic (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (((-(((n : ℝ) + 1) * t ^ 2 / 2)) : ℝ) : ℂ)

/-- A law-level characterization of the centered Gaussian `N(0, variance)` by
its characteristic function. -/
def prob_14_3_isCenteredGaussianLaw
    (P : ProbabilityMeasure ℝ) (variance : ℝ) : Prop :=
  ∀ t : ℝ,
    thm_14_1_characteristicFunction P t =
      Complex.exp (((-(variance * t ^ 2 / 2)) : ℝ) : ℂ)

/-- The pointwise limit of the characteristic functions of `N(0, n + 1)`:
it equals `1` at the origin and `0` away from the origin. -/
def prob_14_3_limitCharacteristic (t : ℝ) : ℂ :=
  if t = 0 then 1 else 0

/-- The concrete textbook setup for Problem 14.3.

The non-target tightness-to-weak-limit direction remains an explicit support
boundary for the rest of Problem 14.3.  This obligation discharges the
Gaussian characteristic-function limit at theorem level instead of assuming it
as a structure field. -/
structure prob_14_3_GaussianVarianceEscapeSetup where
  gaussianLaws : ℕ → ProbabilityMeasure ℝ
  gaussian_law :
    ∀ n : ℕ,
      prob_14_3_isCenteredGaussianLaw (gaussianLaws n) ((n : ℝ) + 1)
  tight_to_weak_by_levy :
    thm_14_1_tight gaussianLaws → thm_14_1_weakLimit gaussianLaws

/-- The Gaussian-law field gives the displayed characteristic function
`exp(-(n+1)t^2/2)`. -/
theorem prob_14_3_gaussian_characteristic
    (S : prob_14_3_GaussianVarianceEscapeSetup) (n : ℕ) (t : ℝ) :
    thm_14_1_characteristicFunction (S.gaussianLaws n) t =
      prob_14_3_gaussianCharacteristic n t := by
  simpa [prob_14_3_gaussianCharacteristic] using S.gaussian_law n t

/-- The displayed Gaussian characteristic functions converge pointwise to
the discontinuous step limit. -/
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

/-- The step function obtained as the pointwise characteristic-function limit
is not continuous at zero. -/
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

/-- Since every characteristic function is continuous at zero, the limiting
step function is not a characteristic function. -/
theorem prob_14_3_limitCharacteristic_not_characteristic :
    ¬ thm_14_1_limitIsCharacteristic prob_14_3_limitCharacteristic := by
  intro hchar
  exact prob_14_3_limitCharacteristic_not_continuousAtZero
    (thm_14_1_characteristic_continuousAtZero hchar)

/-- The Gaussian sequence cannot converge weakly: a weak limit together with
the pointwise characteristic-function limit would make the discontinuous limit
a characteristic function. -/
theorem prob_14_3_not_weakLimit
    (S : prob_14_3_GaussianVarianceEscapeSetup) :
    ¬ thm_14_1_weakLimit S.gaussianLaws := by
  intro hweak
  exact prob_14_3_limitCharacteristic_not_characteristic
    ((thm_14_1_weak_iff_characteristic
      (prob_14_3_gaussian_characteristic_limit S)).mp hweak)

/-- The sequence is not tight.  This is the fourth failed condition in
Lévy's theorem, obtained from the tightness-to-weak-limit direction already
isolated in the chapter interface. -/
theorem prob_14_3_not_tight
    (S : prob_14_3_GaussianVarianceEscapeSetup) :
    ¬ thm_14_1_tight S.gaussianLaws := by
  intro htight
  exact prob_14_3_not_weakLimit S (S.tight_to_weak_by_levy htight)

/-- Problem 14.3: for `X_n ∼ N(0,n)` the sequence fails all four conditions
in Lévy's continuity theorem. -/
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
