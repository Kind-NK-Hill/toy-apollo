/-
TASK ID: prob_10_8
TYPE: Problem
SOURCE PLAN: chapter10-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_4

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable def squareUniformLimitCdf (x : ℝ) : ℝ :=
  if x < 0 then 0 else if x ≤ 1 then Real.sqrt x else 1

noncomputable def prob_10_8_finiteSquareUniformCdf (n : ℕ) (x : ℝ) : ℝ :=
  if x < 0 then
    0
  else if x ≤ 1 then
    (Nat.floor (((n : ℝ) + 1) * Real.sqrt x) : ℝ) / ((n : ℝ) + 1)
  else
    1

private lemma prob_10_8_floor_ratio_tendsto (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (Nat.floor (((n : ℝ) + 1) * Real.sqrt x) : ℝ) / ((n : ℝ) + 1))
      atTop (nhds (Real.sqrt x)) := by
  have hN : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop (atTop : Filter ℝ) := by
    simpa using
      (tendsto_atTop_add_const_right (atTop : Filter ℕ) (1 : ℝ)
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hfloor :
      Tendsto (fun y : ℝ => (Nat.floor (Real.sqrt x * y) : ℝ) / y)
        atTop (nhds (Real.sqrt x)) :=
    tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := Real.sqrt x)
      (Real.sqrt_nonneg x)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hfloor.comp hN

private lemma prob_10_8_finiteSquareUniformCdf_eq_zero_of_lt_zero
    {x : ℝ} (hx : x < 0) :
    (fun n : ℕ => prob_10_8_finiteSquareUniformCdf n x) =
      fun _ : ℕ => 0 := by
  funext n
  simp [prob_10_8_finiteSquareUniformCdf, hx]

private lemma prob_10_8_finiteSquareUniformCdf_eq_floor_of_mem_Icc
    {x : ℝ} (hx0 : ¬ x < 0) (hx1 : x ≤ 1) :
    (fun n : ℕ => prob_10_8_finiteSquareUniformCdf n x) =
      fun n : ℕ =>
        (Nat.floor (((n : ℝ) + 1) * Real.sqrt x) : ℝ) / ((n : ℝ) + 1) := by
  funext n
  simp [prob_10_8_finiteSquareUniformCdf, hx0, hx1]

private lemma prob_10_8_finiteSquareUniformCdf_eq_one_of_one_lt
    {x : ℝ} (hx0 : ¬ x < 0) (hx1 : ¬ x ≤ 1) :
    (fun n : ℕ => prob_10_8_finiteSquareUniformCdf n x) =
      fun _ : ℕ => 1 := by
  funext n
  simp [prob_10_8_finiteSquareUniformCdf, hx0, hx1]

theorem prob_10_8 :
    CdfConvergesInDistribution
      prob_10_8_finiteSquareUniformCdf squareUniformLimitCdf := by
  intro x _hcont
  by_cases hxneg : x < 0
  · have hseq := prob_10_8_finiteSquareUniformCdf_eq_zero_of_lt_zero hxneg
    have hlim :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
          (nhds (squareUniformLimitCdf x)) := by
      simpa [squareUniformLimitCdf, hxneg] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    simpa [hseq] using hlim
  · by_cases hxle : x ≤ 1
    · have hseq :=
        prob_10_8_finiteSquareUniformCdf_eq_floor_of_mem_Icc hxneg hxle
      have hlim := prob_10_8_floor_ratio_tendsto x
      have htarget : squareUniformLimitCdf x = Real.sqrt x := by
        simp [squareUniformLimitCdf, hxneg, hxle]
      simpa [hseq, htarget] using hlim
    · have hseq :=
        prob_10_8_finiteSquareUniformCdf_eq_one_of_one_lt hxneg hxle
      have hlim :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
            (nhds (squareUniformLimitCdf x)) := by
        simpa [squareUniformLimitCdf, hxneg, hxle] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
      simpa [hseq] using hlim
