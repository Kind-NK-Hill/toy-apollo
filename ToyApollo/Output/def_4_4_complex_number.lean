/-
TASK ID: def_4_4_complex_number
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

def complexRealPart (z : ℂ) : ℝ := z.re

def complexImagPart (z : ℂ) : ℝ := z.im

def complexToPair (z : ℂ) : ℝ × ℝ := (z.re, z.im)

def pairToComplex (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

noncomputable def complexEquivRealProd : ℂ ≃ ℝ × ℝ :=
  Complex.equivRealProd

noncomputable def complexHomeomorphRealProd : Homeomorph ℂ (ℝ × ℝ) :=
  Complex.equivRealProdCLM.toHomeomorph

noncomputable def complexMeasurableEquivRealProd : ℂ ≃ᵐ (ℝ × ℝ) :=
  complexHomeomorphRealProd.toMeasurableEquiv

def complexOpenRectangle (a b c d : ℝ) : Set ℂ :=
  {z : ℂ | a < z.re ∧ z.re < b ∧ c < z.im ∧ z.im < d}

theorem pairToComplex_complexToPair (z : ℂ) : pairToComplex (complexToPair z) = z := by
  apply Complex.ext <;> simp [pairToComplex, complexToPair]

theorem complexToPair_pairToComplex (p : ℝ × ℝ) : complexToPair (pairToComplex p) = p := by
  cases p
  simp [pairToComplex, complexToPair]

theorem measurable_complexToPair : Measurable complexToPair := by
  fun_prop

theorem measurable_pairToComplex : Measurable pairToComplex := by
  have h : Measurable (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
    fun_prop
  simpa [pairToComplex] using h

theorem isOpen_complexOpenRectangle (a b c d : ℝ) : IsOpen (complexOpenRectangle a b c d) := by
  simpa [complexOpenRectangle] using
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))

theorem measurableSet_complexOpenRectangle (a b c d : ℝ) :
    MeasurableSet (complexOpenRectangle a b c d) :=
  (isOpen_complexOpenRectangle a b c d).measurableSet
