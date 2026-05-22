/-
TASK ID: ex_14_4_3
TYPE: Example_Proof
SOURCE PLAN: chapter14-central-limit-theorems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.prob_6_3
import ToyApollo.Output.thm_14_7
import ToyApollo.Output.thm_14_8

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

def ex_14_4_3_couponTypes (n : ℕ) : ℕ :=
  n + 2

def ex_14_4_3_targetDistinct (n : ℕ) : ℕ :=
  (ex_14_4_3_couponTypes n + 1) / 2

def ex_14_4_3_successProbability
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) : ℝ :=
  Prob63Support.stageSuccessProb (ex_14_4_3_couponTypes n) i

def ex_14_4_3_geometricMgf (p t : ℝ) : ℝ :=
  p * Real.exp t / (1 - (1 - p) * Real.exp t)

def ex_14_4_3_geometricMean (p : ℝ) : ℝ :=
  1 / p

def ex_14_4_3_geometricVariance (p : ℝ) : ℝ :=
  (1 - p) / p ^ 2

def ex_14_4_3_geometricCenteredFourthMoment (p : ℝ) : ℝ :=
  (1 / p ^ 4) * (1 - p) * (p ^ 2 - 9 * p + 9)

def ex_14_4_3_couponMean (n : ℕ) : ℝ :=
  Prob63Support.couponCollectorValueReal
    (ex_14_4_3_couponTypes n) (ex_14_4_3_targetDistinct n)

def ex_14_4_3_asymptoticMeanScale (n : ℕ) : ℝ :=
  (ex_14_4_3_couponTypes n : ℝ) * Real.log 2

def ex_14_4_3_asymptoticVarianceScale (n : ℕ) : ℝ :=
  (ex_14_4_3_couponTypes n : ℝ) * (1 - Real.log 2)

structure ex_14_4_3_CouponTriangularArraySetup where
  theoremSetup : thm_14_8_TriangularArraySetup
  couponStageLaws :
    (n : ℕ) → Fin (ex_14_4_3_targetDistinct n) → ProbabilityMeasure ℝ
  couponCollectionLaws : ℕ → ProbabilityMeasure ℝ
  normalizedCouponLaws : ℕ → ProbabilityMeasure ℝ
  standardNormalLaw : ProbabilityMeasure ℝ
  row_length_matches :
    ∀ n : ℕ,
      theoremSetup.arrayNotation.rowLength n = ex_14_4_3_targetDistinct n
  standardized_laws_eq :
    theoremSetup.standardizedSumLaws = normalizedCouponLaws
  standard_normal_eq :
    theoremSetup.standardNormalLaw = standardNormalLaw
  source_stage_laws_are_centered_geometric :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n),
      thm_14_8_lyapunovMoment (couponStageLaws n i) 2 =
        ex_14_4_3_geometricCenteredFourthMoment
          (ex_14_4_3_successProbability n i)
  source_rows_are_independent :
    theoremSetup.source_row_independence_on_common_probability_space
  source_coupon_collection_law_is_stage_sum :
    theoremSetup.source_standardized_sum_law_representation
  source_normalized_law_represents_centered_T :
    theoremSetup.standardizedSumLaws = normalizedCouponLaws

structure ex_14_4_3_GeometricMomentFormulas
    (C : ex_14_4_3_CouponTriangularArraySetup) : Prop where
  mgf_formula :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n), ∀ t : ℝ,
      ex_14_4_3_geometricMgf (ex_14_4_3_successProbability n i) t =
        ex_14_4_3_successProbability n i * Real.exp t /
          (1 - (1 - ex_14_4_3_successProbability n i) * Real.exp t)
  mean_formula :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n),
      ex_14_4_3_geometricMean (ex_14_4_3_successProbability n i) =
        1 / ex_14_4_3_successProbability n i
  variance_formula :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n),
      ex_14_4_3_geometricVariance (ex_14_4_3_successProbability n i) =
        (1 - ex_14_4_3_successProbability n i) /
          ex_14_4_3_successProbability n i ^ 2
  centered_fourth_formula :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n),
      ex_14_4_3_geometricCenteredFourthMoment
          (ex_14_4_3_successProbability n i) =
        (1 / ex_14_4_3_successProbability n i ^ 4) *
          (1 - ex_14_4_3_successProbability n i) *
            (ex_14_4_3_successProbability n i ^ 2 -
              9 * ex_14_4_3_successProbability n i + 9)

structure ex_14_4_3_LyapunovVerification
    (C : ex_14_4_3_CouponTriangularArraySetup) where
  moment_formulas : ex_14_4_3_GeometricMomentFormulas C
  fourthMomentRiemannBound : ℕ → ℝ
  fourth_moment_sum_bound :
    ∀ n : ℕ,
      (∑ i : Fin (ex_14_4_3_targetDistinct n),
        ex_14_4_3_geometricCenteredFourthMoment
          (ex_14_4_3_successProbability n i)) /
          Real.rpow (C.theoremSetup.sn n) 4 ≤
        fourthMomentRiemannBound n
  fourth_moment_riemann_bound_tendsto_zero :
    Tendsto fourthMomentRiemannBound atTop (𝓝 (0 : ℝ))
  variance_asymptotic :
    Tendsto
      (fun n : ℕ =>
        C.theoremSetup.sn n ^ 2 / (ex_14_4_3_couponTypes n : ℝ))
      atTop (𝓝 (1 - Real.log 2))
  mean_asymptotic :
    Tendsto
      (fun n : ℕ =>
        ex_14_4_3_couponMean n / (ex_14_4_3_couponTypes n : ℝ))
      atTop (𝓝 (Real.log 2))
  lyapunov_condition_delta_two :
    thm_14_8_LyapunovCondition C.theoremSetup

theorem ex_14_4_3_asymptoticNormality
    (C : ex_14_4_3_CouponTriangularArraySetup)
    (hLyapunov : thm_14_8_LyapunovCondition C.theoremSetup)
    (H : thm_14_8_ProofBeyondBook C.theoremSetup) :
    Tendsto C.normalizedCouponLaws atTop (𝓝 C.standardNormalLaw) := by
  have hCLT :
      thm_14_8_conclusion C.theoremSetup :=
    thm_14_8 C.theoremSetup H (Or.inr hLyapunov)
  rw [thm_14_8_conclusion, C.standardized_laws_eq, C.standard_normal_eq] at hCLT
  exact hCLT

theorem ex_14_4_3
    (C : ex_14_4_3_CouponTriangularArraySetup)
    (hLyapunov : thm_14_8_LyapunovCondition C.theoremSetup)
    (H : thm_14_8_ProofBeyondBook C.theoremSetup) :
    Tendsto C.normalizedCouponLaws atTop (𝓝 C.standardNormalLaw) :=
  ex_14_4_3_asymptoticNormality C hLyapunov H
