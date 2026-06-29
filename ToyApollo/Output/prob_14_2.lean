import Mathlib
import ToyApollo.Output.prob_9_3
import ToyApollo.Output.thm_14_7

/-
TASK ID: prob_14_2
TYPE: Problem
SOURCE PLAN: chapter14-problems
TASK CONTENT:
\textbf{14.2.} For n = 1 , 2, 3,... ,l e t Xn denote a random variable with distribution

( n \alpha , \beta)Prove that

1\sqrt n\alpha\beta

(

Xn -n\alpha\beta

) D

-\to N( 0,1).
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

/-- Characteristic-function formula for a Gamma law with shape `shape` and
scale `scale`, using the Problem 9.3 same-scale Gamma characteristic formula. -/
def prob_14_2_gammaScaleCharacteristic
    (shape scale t : ℝ) : ℂ :=
  gammaCharacteristicFunctionFormula shape scale t

/-- A law has the Gamma(shape, scale) distribution in the characteristic-
function sense needed for Problem 14.2. -/
def prob_14_2_isGammaShapeScaleLaw
    (law : ProbabilityMeasure ℝ) (shape scale : ℝ) : Prop :=
  ∀ t : ℝ,
    thm_14_1_characteristicFunction law t =
      prob_14_2_gammaScaleCharacteristic shape scale t

/-- The characteristic-function statement that the `n`-th Gamma law is the sum
of `n+1` iid Gamma(α, β) variables. -/
def prob_14_2_iidGammaSumRepresentation
    (alpha beta : ℝ) (gammaLaws : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∀ n : ℕ, ∀ t : ℝ,
    thm_14_1_characteristicFunction (gammaLaws n) t =
      (prob_14_2_gammaScaleCharacteristic alpha beta t) ^ (n + 1)

/-- Same-scale Gamma characteristic functions multiply by adding shapes. -/
theorem prob_14_2_gammaScaleCharacteristic_pow
    (alpha beta t : ℝ) :
    ∀ n : ℕ,
      prob_14_2_gammaScaleCharacteristic ((n + 1 : ℝ) * alpha) beta t =
        (prob_14_2_gammaScaleCharacteristic alpha beta t) ^ (n + 1)
  | 0 => by
      simp [prob_14_2_gammaScaleCharacteristic]
  | n + 1 => by
      have hmul := gammaCharacteristicFunctionFormula_mul_same_scale
        alpha (((n + 1 : ℕ) : ℝ) * alpha) beta t
      have hmul' :
          prob_14_2_gammaScaleCharacteristic alpha beta t *
              prob_14_2_gammaScaleCharacteristic
                (((n + 1 : ℕ) : ℝ) * alpha) beta t =
            prob_14_2_gammaScaleCharacteristic
              (alpha + ((n + 1 : ℕ) : ℝ) * alpha) beta t := by
        simpa [prob_14_2_gammaScaleCharacteristic] using hmul
      have hind := prob_14_2_gammaScaleCharacteristic_pow alpha beta t n
      have hprev :
          prob_14_2_gammaScaleCharacteristic
              (((n + 1 : ℕ) : ℝ) * alpha) beta t =
            (prob_14_2_gammaScaleCharacteristic alpha beta t) ^ (n + 1) := by
        simpa [Nat.cast_add, Nat.cast_one] using hind
      have hshape :
          (((n + 1 : ℕ) : ℝ) + 1) * alpha =
            alpha + ((n + 1 : ℕ) : ℝ) * alpha := by
        ring
      rw [hshape, ← hmul', hprev]
      ring_nf

/-- If each `gammaLaws n` has Gamma((n+1)α, β) characteristic function, then
its characteristic function is the `(n+1)`-fold iid Gamma(α, β) product. -/
theorem prob_14_2_iidGammaSumRepresentation_of_shapeScale
    (alpha beta : ℝ) (gammaLaws : ℕ → ProbabilityMeasure ℝ)
    (hgamma :
      ∀ n : ℕ,
        prob_14_2_isGammaShapeScaleLaw (gammaLaws n)
          ((n + 1 : ℝ) * alpha) beta) :
    prob_14_2_iidGammaSumRepresentation alpha beta gammaLaws := by
  intro n t
  rw [hgamma n t]
  exact prob_14_2_gammaScaleCharacteristic_pow alpha beta t n

/-- Source-facing landing for the Gamma additivity support step used in
Problem 14.2. -/
theorem prob_14_2_gamma_iid_sum_representation
    (alpha beta : ℝ) (gammaLaws : ℕ → ProbabilityMeasure ℝ)
    (hgamma :
      ∀ n : ℕ,
        prob_14_2_isGammaShapeScaleLaw (gammaLaws n)
          ((n + 1 : ℝ) * alpha) beta) :
    prob_14_2_iidGammaSumRepresentation alpha beta gammaLaws :=
  prob_14_2_iidGammaSumRepresentation_of_shapeScale alpha beta gammaLaws hgamma

/-- Focused obligation landing for Problem 14.2: the Gamma source laws have
the characteristic-function product representation of `(n+1)` iid
Gamma(α, β) summands. -/
theorem prob_14_2
    (alpha beta : ℝ) (gammaLaws : ℕ → ProbabilityMeasure ℝ)
    (hgamma :
      ∀ n : ℕ,
        prob_14_2_isGammaShapeScaleLaw (gammaLaws n)
          ((n + 1 : ℝ) * alpha) beta) :
    prob_14_2_iidGammaSumRepresentation alpha beta gammaLaws :=
  prob_14_2_gamma_iid_sum_representation alpha beta gammaLaws hgamma
