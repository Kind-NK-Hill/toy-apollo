/-
TASK ID: def_4_4_complex_operations
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic

theorem complex_addition_equivalence (a b c d : ℝ) :
    Complex.mk a b + Complex.mk c d = Complex.mk (a + c) (b + d) := rfl

noncomputable def complex_abs (z : ℂ) : ℝ := Norm.norm z

local notation "|" z "|" => complex_abs z

theorem complex_triangle_inequality (z1 z2 : ℂ) :
    |z1 + z2| ≤ |z1| + |z2| :=
  norm_add_le z1 z2

theorem complex_multiplication_equivalence (a b c d : ℝ) :
    Complex.mk a b * Complex.mk c d = Complex.mk (a * c - b * d) (a * d + b * c) := rfl

def complex_conjugate (z : ℂ) : ℂ :=
  ⟨z.re, -z.im⟩

postfix:max "∗" => complex_conjugate

theorem complex_conjugate_spec (a b : ℝ) :
    (Complex.mk a b)∗ = Complex.mk a (-b) := rfl
