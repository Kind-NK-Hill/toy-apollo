/-
TASK ID: prob_12_5
TYPE: Problem
SOURCE PLAN: chapter12-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_12_2
import ToyApollo.Output.thm_12_5

-- WRITE FINAL LEAN CODE BELOW

noncomputable section

def prob_12_5_oneSensorMSE (v0 v1 α : ℝ) : ℝ :=
  (1 - α) ^ 2 * v0 + α ^ 2 * v1

def prob_12_5_oneSensorAlpha (v0 v1 : ℝ) : ℝ :=
  v0 / (v0 + v1)

def prob_12_5_twoSensorMSE (v0 v1 v2 α β : ℝ) : ℝ :=
  (1 - α - β) ^ 2 * v0 + α ^ 2 * v1 + β ^ 2 * v2

def prob_12_5_twoSensorDen (v0 v1 v2 : ℝ) : ℝ :=
  v0 * v1 + v0 * v2 + v1 * v2

def prob_12_5_twoSensorAlpha (v0 v1 v2 : ℝ) : ℝ :=
  v0 * v2 / prob_12_5_twoSensorDen v0 v1 v2

def prob_12_5_twoSensorBeta (v0 v1 v2 : ℝ) : ℝ :=
  v0 * v1 / prob_12_5_twoSensorDen v0 v1 v2

theorem prob_12_5_oneSensorMSE_sub_opt
    {v0 v1 : ℝ} (hden : v0 + v1 ≠ 0) (α : ℝ) :
    prob_12_5_oneSensorMSE v0 v1 α -
        prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1) =
      (v0 + v1) * (α - prob_12_5_oneSensorAlpha v0 v1) ^ 2 := by
  unfold prob_12_5_oneSensorMSE prob_12_5_oneSensorAlpha
  field_simp [hden]
  ring_nf

theorem prob_12_5_oneSensorAlpha_optimal
    {v0 v1 : ℝ} (hpos : 0 < v0 + v1) (α : ℝ) :
    prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1) ≤
      prob_12_5_oneSensorMSE v0 v1 α := by
  have hden : v0 + v1 ≠ 0 := ne_of_gt hpos
  have hdiff := prob_12_5_oneSensorMSE_sub_opt (v0 := v0) (v1 := v1) hden α
  have hnonneg :
      0 ≤ prob_12_5_oneSensorMSE v0 v1 α -
        prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1) := by
    rw [hdiff]
    exact mul_nonneg (le_of_lt hpos)
      (sq_nonneg (α - prob_12_5_oneSensorAlpha v0 v1))
  linarith

theorem prob_12_5_twoSensorMSE_sub_stationary
    {v0 v1 v2 α0 β0 : ℝ}
    (hα : v1 * α0 = v0 * (1 - α0 - β0))
    (hβ : v2 * β0 = v0 * (1 - α0 - β0)) (α β : ℝ) :
    prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2 α0 β0 =
      v0 * ((1 - α - β) - (1 - α0 - β0)) ^ 2 +
        v1 * (α - α0) ^ 2 +
        v2 * (β - β0) ^ 2 := by
  have hlinear :
      v0 * (1 - α0 - β0) * ((1 - α - β) - (1 - α0 - β0)) * 2 +
          v1 * α0 * (α - α0) * 2 +
          v2 * β0 * (β - β0) * 2 = 0 := by
    rw [hα, hβ]
    ring
  calc
    prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2 α0 β0 =
      (v0 * ((1 - α - β) - (1 - α0 - β0)) ^ 2 +
          v1 * (α - α0) ^ 2 +
          v2 * (β - β0) ^ 2) +
        (v0 * (1 - α0 - β0) * ((1 - α - β) - (1 - α0 - β0)) * 2 +
          v1 * α0 * (α - α0) * 2 +
          v2 * β0 * (β - β0) * 2) := by
        unfold prob_12_5_twoSensorMSE
        ring
    _ = v0 * ((1 - α - β) - (1 - α0 - β0)) ^ 2 +
        v1 * (α - α0) ^ 2 +
        v2 * (β - β0) ^ 2 := by
      rw [hlinear]
      ring

theorem prob_12_5_twoSensorCoefficients_stationary
    {v0 v1 v2 : ℝ} (hden : prob_12_5_twoSensorDen v0 v1 v2 ≠ 0) :
    v1 * prob_12_5_twoSensorAlpha v0 v1 v2 =
        v0 * (1 - prob_12_5_twoSensorAlpha v0 v1 v2 -
          prob_12_5_twoSensorBeta v0 v1 v2) ∧
      v2 * prob_12_5_twoSensorBeta v0 v1 v2 =
        v0 * (1 - prob_12_5_twoSensorAlpha v0 v1 v2 -
          prob_12_5_twoSensorBeta v0 v1 v2) := by
  let D := prob_12_5_twoSensorDen v0 v1 v2
  have hD : D ≠ 0 := by
    simpa [D] using hden
  have hresidual :
      1 - v0 * v2 / D - v0 * v1 / D = v1 * v2 / D := by
    dsimp [D]
    field_simp [prob_12_5_twoSensorDen, hden]
    unfold prob_12_5_twoSensorDen
    ring_nf
  constructor
  · change v1 * (v0 * v2 / D) =
      v0 * (1 - v0 * v2 / D - v0 * v1 / D)
    rw [hresidual]
    field_simp [hD]
  · change v2 * (v0 * v1 / D) =
      v0 * (1 - v0 * v2 / D - v0 * v1 / D)
    rw [hresidual]
    field_simp [hD]

theorem prob_12_5_twoSensorMSE_sub_opt
    {v0 v1 v2 : ℝ} (hden : prob_12_5_twoSensorDen v0 v1 v2 ≠ 0)
    (α β : ℝ) :
    prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2
          (prob_12_5_twoSensorAlpha v0 v1 v2)
          (prob_12_5_twoSensorBeta v0 v1 v2) =
      v0 *
          ((1 - α - β) -
            (1 - prob_12_5_twoSensorAlpha v0 v1 v2 -
              prob_12_5_twoSensorBeta v0 v1 v2)) ^ 2 +
        v1 * (α - prob_12_5_twoSensorAlpha v0 v1 v2) ^ 2 +
        v2 * (β - prob_12_5_twoSensorBeta v0 v1 v2) ^ 2 := by
  have hstat := prob_12_5_twoSensorCoefficients_stationary
    (v0 := v0) (v1 := v1) (v2 := v2) hden
  exact prob_12_5_twoSensorMSE_sub_stationary
    hstat.1 hstat.2 α β

theorem prob_12_5_twoSensorCoefficients_optimal
    {v0 v1 v2 : ℝ} (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) (hv2 : 0 ≤ v2)
    (hden : prob_12_5_twoSensorDen v0 v1 v2 ≠ 0) (α β : ℝ) :
    prob_12_5_twoSensorMSE v0 v1 v2
        (prob_12_5_twoSensorAlpha v0 v1 v2)
        (prob_12_5_twoSensorBeta v0 v1 v2) ≤
      prob_12_5_twoSensorMSE v0 v1 v2 α β := by
  have hdiff :=
    prob_12_5_twoSensorMSE_sub_opt
      (v0 := v0) (v1 := v1) (v2 := v2) hden α β
  have hnonneg :
      0 ≤ prob_12_5_twoSensorMSE v0 v1 v2 α β -
        prob_12_5_twoSensorMSE v0 v1 v2
          (prob_12_5_twoSensorAlpha v0 v1 v2)
          (prob_12_5_twoSensorBeta v0 v1 v2) := by
    rw [hdiff]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg hv0 (sq_nonneg _))
        (mul_nonneg hv1 (sq_nonneg _)))
      (mul_nonneg hv2 (sq_nonneg _))
  linarith

theorem prob_12_5
    {v0 v1 v2 : ℝ} (hv0 : 0 < v0) (hv1 : 0 < v1) (hv2 : 0 < v2) :
    (∀ α : ℝ,
      prob_12_5_oneSensorMSE v0 v1 (prob_12_5_oneSensorAlpha v0 v1) ≤
        prob_12_5_oneSensorMSE v0 v1 α) ∧
    (∀ α β : ℝ,
      prob_12_5_twoSensorMSE v0 v1 v2
          (prob_12_5_twoSensorAlpha v0 v1 v2)
          (prob_12_5_twoSensorBeta v0 v1 v2) ≤
        prob_12_5_twoSensorMSE v0 v1 v2 α β) := by
  constructor
  · intro α
    exact prob_12_5_oneSensorAlpha_optimal
      (v0 := v0) (v1 := v1) (by positivity) α
  · intro α β
    have hden_pos : 0 < prob_12_5_twoSensorDen v0 v1 v2 := by
      have h01 : 0 < v0 * v1 := mul_pos hv0 hv1
      have h02 : 0 < v0 * v2 := mul_pos hv0 hv2
      have h12 : 0 < v1 * v2 := mul_pos hv1 hv2
      unfold prob_12_5_twoSensorDen
      nlinarith [h01, h02, h12]
    exact prob_12_5_twoSensorCoefficients_optimal
      (v0 := v0) (v1 := v1) (v2 := v2)
      (le_of_lt hv0) (le_of_lt hv1) (le_of_lt hv2)
      (ne_of_gt hden_pos) α β
