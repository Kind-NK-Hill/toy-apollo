/-
TASK ID: ex_1_3_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory intervalIntegral
open scoped Real

noncomputable section

def mixedDiscretePart (p : ℝ) : ℝ → ℝ :=
  fun x =>
    p * Set.indicator (Set.Ici (-3 / 2 : ℝ)) (fun _ => (1 : ℝ)) x +
      p * Set.indicator (Set.Ici (3 / 2 : ℝ)) (fun _ => (1 : ℝ)) x

def standardNormalKernel (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

def mixedContinuousPart (p : ℝ) : ℝ → ℝ :=
  fun x =>
    if x < (-3 / 2 : ℝ) then 0
    else if x < (3 / 2 : ℝ) then
      (1 - 2 * p) * ∫ t in (-3 / 2 : ℝ)..x, standardNormalKernel t
    else 1 - 2 * p

def mixedDiscreteExpectation (p : ℝ) : ℝ :=
  (-3 / 2 : ℝ) * p + (3 / 2 : ℝ) * p

def mixedContinuousExpectation (p : ℝ) : ℝ :=
  ∫ y in (-(3 / 2 : ℝ))..(3 / 2 : ℝ), y * ((1 - 2 * p) * standardNormalKernel y)

structure MixedTypeExpectationData where
  discretePart : ℝ → ℝ
  continuousPart : ℝ → ℝ
  discreteContribution : ℝ
  continuousContribution : ℝ

def ex_1_3_2 (p : ℝ) : MixedTypeExpectationData where
  discretePart := mixedDiscretePart p
  continuousPart := mixedContinuousPart p
  discreteContribution := mixedDiscreteExpectation p
  continuousContribution := mixedContinuousExpectation p

theorem standardNormalKernel_even (x : ℝ) :
    standardNormalKernel (-x) = standardNormalKernel x := by
  simp [standardNormalKernel, neg_sq]

theorem mixedContinuousIntegrand_odd (p x : ℝ) :
    (-x) * ((1 - 2 * p) * standardNormalKernel (-x)) =
      -(x * ((1 - 2 * p) * standardNormalKernel x)) := by
  rw [standardNormalKernel_even]
  ring

theorem mixedDiscreteExpectation_eq_zero (p : ℝ) :
    mixedDiscreteExpectation p = 0 := by
  unfold mixedDiscreteExpectation
  ring

theorem mixedContinuousExpectation_eq_zero (p : ℝ) :
    mixedContinuousExpectation p = 0 := by
  let c : ℝ := 3 / 2
  let g : ℝ → ℝ := fun y => y * ((1 - 2 * p) * standardNormalKernel y)
  have hcomp :
      ∫ x in (-c : ℝ)..c, g (-x) = mixedContinuousExpectation p := by
    simpa [c, g, mixedContinuousExpectation] using
      (intervalIntegral.integral_comp_neg (f := g) (a := (-c : ℝ)) (b := c))
  have hodd :
      ∫ x in (-c : ℝ)..c, g (-x) = -mixedContinuousExpectation p := by
    calc
      ∫ x in (-c : ℝ)..c, g (-x)
          = ∫ x in (-c : ℝ)..c, -g x := by
              congr with x
              have hx := mixedContinuousIntegrand_odd p x
              simpa [g] using hx
      _ = -∫ x in (-c : ℝ)..c, g x := by rw [intervalIntegral.integral_neg]
      _ = -mixedContinuousExpectation p := by
            simp [c, g, mixedContinuousExpectation]
  have hself : mixedContinuousExpectation p = -mixedContinuousExpectation p := by
    calc
      mixedContinuousExpectation p = ∫ x in (-c : ℝ)..c, g (-x) := by simpa using hcomp.symm
      _ = -mixedContinuousExpectation p := hodd
  linarith

theorem ex_1_3_2_expectation_split (p : ℝ) :
    (ex_1_3_2 p).discreteContribution + (ex_1_3_2 p).continuousContribution = 0 := by
  change mixedDiscreteExpectation p + mixedContinuousExpectation p = 0
  rw [mixedDiscreteExpectation_eq_zero, mixedContinuousExpectation_eq_zero]
  ring

theorem ex_1_3_2_mean_zero (p : ℝ) :
    (ex_1_3_2 p).discreteContribution + (ex_1_3_2 p).continuousContribution = 0 := by
  exact ex_1_3_2_expectation_split p
