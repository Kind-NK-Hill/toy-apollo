/-
TASK ID: def_4_4_complex_random_variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_4_4_complex_number
import ToyApollo.Output.def_4_4_complex_operations

open MeasureTheory

def IsComplexRandomVariable {Ω : Type*} [MeasurableSpace Ω] (Z : Ω → ℂ) : Prop :=
  Measurable Z

theorem isComplexRandomVariable_iff_measurable {Ω : Type*} [MeasurableSpace Ω] (Z : Ω → ℂ) :
    IsComplexRandomVariable Z ↔ Measurable Z :=
  Iff.rfl

def complexRealPartRV {Ω : Type*} [MeasurableSpace Ω] (Z : Ω → ℂ) : Ω → ℝ :=
  fun ω => complexRealPart (Z ω)

def complexImagPartRV {Ω : Type*} [MeasurableSpace Ω] (Z : Ω → ℂ) : Ω → ℝ :=
  fun ω => complexImagPart (Z ω)

def complexConjugateRV {Ω : Type*} [MeasurableSpace Ω] (Z : Ω → ℂ) : Ω → ℂ :=
  fun ω => complex_conjugate (Z ω)

theorem measurable_complexConjugateRV {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℂ}
    (hZ : IsComplexRandomVariable Z) : Measurable (complexConjugateRV Z) := by
  simpa [IsComplexRandomVariable, complexConjugateRV, complex_conjugate] using
    (continuous_star.measurable.comp hZ)

theorem measurable_complexRealPartRV {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℂ}
    (hZ : IsComplexRandomVariable Z) : Measurable (complexRealPartRV Z) := by
  simpa [complexRealPartRV, IsComplexRandomVariable, complexRealPart] using
    (Complex.continuous_re.measurable.comp hZ)

theorem measurable_complexImagPartRV {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℂ}
    (hZ : IsComplexRandomVariable Z) : Measurable (complexImagPartRV Z) := by
  simpa [complexImagPartRV, IsComplexRandomVariable, complexImagPart] using
    (Complex.continuous_im.measurable.comp hZ)

theorem isComplexRandomVariable_of_measurable_parts {Ω : Type*} [MeasurableSpace Ω] {Z : Ω → ℂ}
    (hRe : Measurable (complexRealPartRV Z)) (hIm : Measurable (complexImagPartRV Z)) :
    IsComplexRandomVariable Z := by
  have hPair : Measurable (fun ω => (complexRealPartRV Z ω, complexImagPartRV Z ω)) :=
    Measurable.prodMk hRe hIm
  change Measurable Z
  convert
    (show Measurable (fun ω => pairToComplex (complexRealPartRV Z ω, complexImagPartRV Z ω)) from
      measurable_pairToComplex.comp hPair) using 1
  funext ω
  simpa [complexRealPartRV, complexImagPartRV, complexToPair] using
    (pairToComplex_complexToPair (Z ω)).symm

theorem isComplexRandomVariable_iff_measurable_parts {Ω : Type*} [MeasurableSpace Ω]
    {Z : Ω → ℂ} :
    IsComplexRandomVariable Z ↔
      Measurable (complexRealPartRV Z) ∧ Measurable (complexImagPartRV Z) := by
  constructor
  · intro hZ
    exact ⟨measurable_complexRealPartRV hZ, measurable_complexImagPartRV hZ⟩
  · rintro ⟨hRe, hIm⟩
    exact isComplexRandomVariable_of_measurable_parts hRe hIm
