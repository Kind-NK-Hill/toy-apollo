/-
TASK ID: def_6_6
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap







open MeasureTheory



def complexTextbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Prop :=
  Integrable (fun ω => (Z ω).re) μ ∧ Integrable (fun ω => (Z ω).im) μ



theorem complexTextbookIntegrable_iff_integrable_core {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) :
    complexTextbookIntegrable μ Z ↔ Integrable Z μ := by
  unfold complexTextbookIntegrable
  exact (MeasureTheory.Integrable.re_im_iff (μ := μ) (f := Z))

 
noncomputable def complexTextbookIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Option ℂ := by
  classical
  exact
    if hZ : complexTextbookIntegrable μ Z then
      some
        (Complex.ofReal (∫ ω, (Z ω).re ∂μ) +
          Complex.I * Complex.ofReal (∫ ω, (Z ω).im ∂μ))
    else
      none

 
noncomputable def def_6_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → ℂ) :
    Option ℂ :=
  complexTextbookIntegral μ Z

theorem complexTextbookIntegral_eq_none_of_not_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : ¬ complexTextbookIntegrable μ Z) :
    complexTextbookIntegral μ Z = none := by
  classical
  simp [complexTextbookIntegral, hZ]

theorem complexTextbookIntegral_eq_some_of_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : complexTextbookIntegrable μ Z) :
    ∃ w : ℂ, complexTextbookIntegral μ Z = some w := by
  refine ⟨∫ ω, Z ω ∂μ, ?_⟩
  have hZ' : Integrable Z μ :=
    (complexTextbookIntegrable_iff_integrable_core μ Z).mp hZ
  unfold complexTextbookIntegral
  rw [dif_pos hZ]
  apply congrArg some
  simpa [mul_comm] using (integral_re_add_im hZ')


theorem complexTextbookIntegral_eq_some_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) (hZ : complexTextbookIntegrable μ Z) :
    complexTextbookIntegral μ Z = some (∫ ω, Z ω ∂μ) := by
  have hZ' : Integrable Z μ :=
    (complexTextbookIntegrable_iff_integrable_core μ Z).mp hZ
  unfold complexTextbookIntegral
  rw [dif_pos hZ]
  apply congrArg some
  simpa [mul_comm] using (integral_re_add_im hZ')
