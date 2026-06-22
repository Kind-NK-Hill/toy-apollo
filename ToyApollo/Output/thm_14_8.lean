/-
TASK ID: thm_14_8
TYPE: Theorem_Statement
SOURCE PLAN: chapter14-central-limit-theorems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.chapter14_triangular_array_support

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section

abbrev thm_14_8_TriangularArrayNotation :=
  chapter14_TriangularArrayNotation

def thm_14_8_lindebergTailIntegral
    (μ : ProbabilityMeasure ℝ) (threshold : ℝ) : ℝ :=
  ∫ x in {x : ℝ | threshold ≤ |x|}, x ^ 2 ∂(μ : Measure ℝ)

def thm_14_8_lyapunovMoment
    (μ : ProbabilityMeasure ℝ) (δ : ℝ) : ℝ :=
  ∫ x, Real.rpow |x| (2 + δ) ∂(μ : Measure ℝ)

structure thm_14_8_TriangularArraySetup where
  arrayNotation : thm_14_8_TriangularArrayNotation
  rowLaws : (n : ℕ) → Fin (arrayNotation.rowLength n) → ProbabilityMeasure ℝ
  standardizedSumLaws : ℕ → ProbabilityMeasure ℝ
  standardNormalLaw : ProbabilityMeasure ℝ
  sn : ℕ → ℝ
  sn_pos : ∀ n : ℕ, 0 < sn n
  sn_sq_eq_totalVariance :
    ∀ n : ℕ, sn n ^ 2 = arrayNotation.totalVariance n
  sn_tendsto_atTop : Tendsto sn atTop atTop
  row_mean_zero :
    ∀ n : ℕ, ∀ i : Fin (arrayNotation.rowLength n),
      ∫ x, x ∂((rowLaws n i : ProbabilityMeasure ℝ) : Measure ℝ) = 0
  row_variance_eq_second_moment :
    ∀ n : ℕ, ∀ i : Fin (arrayNotation.rowLength n),
      arrayNotation.variance n i =
        ∫ x, x ^ 2 ∂((rowLaws n i : ProbabilityMeasure ℝ) : Measure ℝ)
  source_row_independence_on_common_probability_space : Prop
  source_standardized_sum_law_representation : Prop

def thm_14_8_LindebergCondition
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun n : ℕ =>
        (∑ i : Fin (S.arrayNotation.rowLength n),
          thm_14_8_lindebergTailIntegral (S.rowLaws n i) (ε * S.sn n)) /
            (S.sn n ^ 2))
      atTop (𝓝 (0 : ℝ))

def thm_14_8_LyapunovCondition
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    Tendsto
      (fun n : ℕ =>
        (∑ i : Fin (S.arrayNotation.rowLength n),
          thm_14_8_lyapunovMoment (S.rowLaws n i) δ) /
            Real.rpow (S.sn n) (2 + δ))
      atTop (𝓝 (0 : ℝ))

def thm_14_8_condition
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  thm_14_8_LindebergCondition S ∨ thm_14_8_LyapunovCondition S

def thm_14_8_conclusion
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  Tendsto S.standardizedSumLaws atTop (𝓝 S.standardNormalLaw)

structure thm_14_8_ProofBeyondBook
    (S : thm_14_8_TriangularArraySetup) : Prop where
  lindeberg_triangular_array_clt :
    thm_14_8_LindebergCondition S → thm_14_8_conclusion S
  lyapunov_implies_lindeberg :
    thm_14_8_LyapunovCondition S → thm_14_8_LindebergCondition S

theorem thm_14_8_of_lindeberg
    (S : thm_14_8_TriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook S)
    (hL : thm_14_8_LindebergCondition S) :
    thm_14_8_conclusion S :=
  H.lindeberg_triangular_array_clt hL

theorem thm_14_8_of_lyapunov
    (S : thm_14_8_TriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook S)
    (hY : thm_14_8_LyapunovCondition S) :
    thm_14_8_conclusion S :=
  H.lindeberg_triangular_array_clt (H.lyapunov_implies_lindeberg hY)

theorem thm_14_8
    (S : thm_14_8_TriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook S)
    (h : thm_14_8_condition S) :
    thm_14_8_conclusion S := by
  rcases h with hL | hY
  · exact thm_14_8_of_lindeberg S H hL
  · exact thm_14_8_of_lyapunov S H hY
