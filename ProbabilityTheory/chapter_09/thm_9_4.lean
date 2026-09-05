/-
TASK ID: thm_9_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter9-characteristic-functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_09.def_9_3




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped Interval

private lemma thm_9_4_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ ≤ x := by
  have h_int :
      (∫ u in (0 : ℝ)..x, Complex.exp (Complex.I * (u : ℂ))) =
        (Complex.exp (Complex.I * (x : ℂ)) - 1) / Complex.I := by
    simpa using
      (integral_exp_mul_complex
        (a := (0 : ℝ)) (b := x) (c := Complex.I) (by simp))
  have h_norm_eq :
      ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ =
        ‖∫ u in (0 : ℝ)..x, Complex.exp (Complex.I * (u : ℂ))‖ := by
    calc
      ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ =
          ‖(Complex.exp (Complex.I * (x : ℂ)) - 1) / Complex.I‖ := by
        simp
      _ = ‖∫ u in (0 : ℝ)..x, Complex.exp (Complex.I * (u : ℂ))‖ := by
        rw [h_int]
  have h_triangle :
      ‖∫ u in (0 : ℝ)..x, Complex.exp (Complex.I * (u : ℂ))‖ ≤
        ∫ u in (0 : ℝ)..x, ‖Complex.exp (Complex.I * (u : ℂ))‖ :=
    intervalIntegral.norm_integral_le_integral_norm hx
  have h_norm_integral :
      (∫ u in (0 : ℝ)..x, ‖Complex.exp (Complex.I * (u : ℂ))‖) = x := by
    simp [Complex.norm_exp_I_mul_ofReal]
  rw [h_norm_eq]
  exact h_triangle.trans_eq h_norm_integral

private lemma thm_9_4_neg_reduce (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ =
      ‖Complex.exp (Complex.I * ((-x) : ℂ)) - 1‖ := by
  have hprod :
      Complex.exp (Complex.I * (x : ℂ)) *
          Complex.exp (Complex.I * ((-x) : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    have hzero : Complex.I * (x : ℂ) + Complex.I * ((-x) : ℂ) = 0 := by
      ring
    rw [hzero]
    simp
  calc
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ =
        ‖1 - Complex.exp (Complex.I * (x : ℂ))‖ := norm_sub_rev _ _
    _ = ‖Complex.exp (Complex.I * (x : ℂ)) *
          (Complex.exp (Complex.I * ((-x) : ℂ)) - 1)‖ := by
        congr 1
        calc
          1 - Complex.exp (Complex.I * (x : ℂ)) =
              Complex.exp (Complex.I * (x : ℂ)) *
                Complex.exp (Complex.I * ((-x) : ℂ)) -
              Complex.exp (Complex.I * (x : ℂ)) := by
            rw [hprod]
          _ = Complex.exp (Complex.I * (x : ℂ)) *
              (Complex.exp (Complex.I * ((-x) : ℂ)) - 1) := by
            ring
    _ = ‖Complex.exp (Complex.I * (x : ℂ))‖ *
          ‖Complex.exp (Complex.I * ((-x) : ℂ)) - 1‖ := by
        rw [norm_mul]
    _ = ‖Complex.exp (Complex.I * ((-x) : ℂ)) - 1‖ := by
        simp [Complex.norm_exp_I_mul_ofReal]

theorem thm_9_4 (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ ≤ |x| := by
  by_cases hx : 0 ≤ x
  · exact (thm_9_4_nonneg hx).trans_eq (abs_of_nonneg hx).symm
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hnonneg : 0 ≤ -x := by
      linarith
    calc
      ‖Complex.exp (Complex.I * (x : ℂ)) - 1‖ =
          ‖Complex.exp (Complex.I * ((-x) : ℂ)) - 1‖ := thm_9_4_neg_reduce x
      _ ≤ -x := by
        simpa using thm_9_4_nonneg hnonneg
      _ = |x| := (abs_of_neg hxlt).symm
