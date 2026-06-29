import Mathlib
import ToyApollo.Output.def_4_4_complex_random_variable

open MeasureTheory

theorem measurable_pos_imaginary_eigenvalue {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}
    (hX : Measurable X) :
    IsComplexRandomVariable (fun ω => Complex.I * ((X ω : ℂ))) := by
  have hXc : Measurable (fun ω => ((X ω : ℂ))) := Complex.measurable_ofReal.comp hX
  simpa [IsComplexRandomVariable] using (hXc.const_mul Complex.I)

theorem measurable_neg_imaginary_eigenvalue {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}
    (hX : Measurable X) :
    IsComplexRandomVariable (fun ω => -Complex.I * ((X ω : ℂ))) := by
  have hXc : Measurable (fun ω => ((X ω : ℂ))) := Complex.measurable_ofReal.comp hX
  simpa [IsComplexRandomVariable] using (hXc.const_mul (-Complex.I))

/-- Minimal packaged conclusion of Example 4.4.2. -/
theorem ex_4_4_2 {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ} (hX : Measurable X) :
    IsComplexRandomVariable (fun ω => Complex.I * ((X ω : ℂ))) ∧
      IsComplexRandomVariable (fun ω => -Complex.I * ((X ω : ℂ))) := by
  exact ⟨measurable_pos_imaginary_eigenvalue hX, measurable_neg_imaginary_eigenvalue hX⟩
