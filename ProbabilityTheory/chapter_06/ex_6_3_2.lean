/-
TASK ID: ex_6_3_2
TYPE: Example_Proof
SOURCE PLAN: 21_chap6_real_complex_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic




-- WRITE FINAL LEAN CODE BELOW

open intervalIntegral Complex

 
noncomputable def complexPhi (t : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, Complex.exp (((t : ℂ) * Complex.I) * x)



theorem ex_6_3_2 (t : ℝ) (ht : t ≠ 0) :
    complexPhi t = (Complex.I - Complex.I * Complex.exp ((t : ℂ) * Complex.I)) / (t : ℂ) := by
  have htC : ((t : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  rw [complexPhi, integral_exp_mul_complex htC]
  field_simp [ht]
  ring_nf
  simp [Complex.exp_mul_I]
  ring
