/-
TASK ID: def_4_4_complex_number
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.FunProp




 
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
  change Measurable (fun z : ℂ => (z.re, z.im))
  exact Complex.measurable_re.prodMk Complex.measurable_im

theorem measurable_pairToComplex : Measurable pairToComplex := by
  change Measurable (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
  fun_prop

theorem isOpen_complexOpenRectangle (a b c d : ℝ) : IsOpen (complexOpenRectangle a b c d) := by
  simpa only [complexOpenRectangle, Set.setOf_and] using
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))

theorem measurableSet_complexOpenRectangle (a b c d : ℝ) :
    MeasurableSet (complexOpenRectangle a b c d) :=
  (isOpen_complexOpenRectangle a b c d).measurableSet
