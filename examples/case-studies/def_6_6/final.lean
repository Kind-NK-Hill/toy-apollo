import Mathlib

/-!
Sanitized public Interface slice for case study `def_6_6`.
The private source excerpt and prompt-pack metadata are omitted.
-/

open MeasureTheory

/-- Reviewed gate: standard integrability of both actual components. -/
def reviewedComplexIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) : Prop :=
  Integrable (fun ω => (Z ω).re) μ ∧ Integrable (fun ω => (Z ω).im) μ

theorem reviewedComplexIntegrableIff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) :
    reviewedComplexIntegrable μ Z ↔ Integrable Z μ := by
  unfold reviewedComplexIntegrable
  exact (MeasureTheory.Integrable.re_im_iff (μ := μ) (f := Z))

/-- Undefinedness remains explicit outside the reviewed gate. -/
noncomputable def reviewedComplexIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) : Option ℂ := by
  classical
  exact
    if reviewedComplexIntegrable μ Z then
      some
        (Complex.ofReal (∫ ω, (Z ω).re ∂μ) +
          Complex.I * Complex.ofReal (∫ ω, (Z ω).im ∂μ))
    else
      none

theorem reviewedComplexIntegralEqSomeIntegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ)
    (hZ : reviewedComplexIntegrable μ Z) :
    reviewedComplexIntegral μ Z = some (∫ ω, Z ω ∂μ) := by
  have hZ' : Integrable Z μ := (reviewedComplexIntegrableIff μ Z).mp hZ
  unfold reviewedComplexIntegral
  rw [if_pos hZ]
  apply congrArg some
  simpa [mul_comm] using integral_re_add_im hZ'
