/-
TASK ID: def_4_4_polar_form
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_4_4_complex_number
import ToyApollo.Output.def_4_4_complex_operations
import ToyApollo.Output.def_4_4_complex_random_variable

noncomputable def complexRadius (z : ℂ) : ℝ :=
  complex_abs z

def complexArgumentDefined (z : ℂ) : Prop :=
  z ≠ 0

noncomputable def complexPrincipalArgument (z : ℂ) : ℝ :=
  Complex.arg z

noncomputable def complexArgument (z : ℂ) : Option ℝ :=
  by
    classical
    exact if hz : complexArgumentDefined z then some (complexPrincipalArgument z) else none

noncomputable def complexPhase (z : ℂ) : Option Real.Angle :=
  (complexArgument z).map fun θ => (θ : Real.Angle)

noncomputable def complexPolarData (z : ℂ) : ℝ × Option ℝ :=
  (complexRadius z, complexArgument z)

noncomputable def complexPolarPhaseData (z : ℂ) : ℝ × Option Real.Angle :=
  (complexRadius z, complexPhase z)

noncomputable def complexOfPolar (r θ : ℝ) : ℂ :=
  Complex.mk (r * Real.cos θ) (r * Real.sin θ)

noncomputable def complexPolarRV {Ω : Type*} (Z : Ω → ℂ) : Ω → (ℝ × Option ℝ) :=
  fun ω => complexPolarData (Z ω)

noncomputable def complexPhaseRV {Ω : Type*} (Z : Ω → ℂ) : Ω → Option Real.Angle :=
  fun ω => complexPhase (Z ω)

theorem complexArgument_not_defined_at_zero : ¬ complexArgumentDefined 0 := by
  simp [complexArgumentDefined]

theorem complexArgument_undefined_at_zero :
    complexArgument 0 = none := by
  simp [complexArgument, complexArgumentDefined]

theorem complexPhase_undefined_at_zero :
    complexPhase 0 = none := by
  simp [complexPhase, complexArgument_undefined_at_zero]

theorem complexArgument_some_of_defined {z : ℂ} (hz : complexArgumentDefined z) :
    complexArgument z = some (complexPrincipalArgument z) := by
  simp [complexArgument, hz]

theorem complexPhase_some_of_defined {z : ℂ} (hz : complexArgumentDefined z) :
    complexPhase z = some (complexPrincipalArgument z : Real.Angle) := by
  simp [complexPhase, complexArgument_some_of_defined hz]

theorem complexArgument_eq_none_iff (z : ℂ) :
    complexArgument z = none ↔ ¬ complexArgumentDefined z := by
  by_cases hz : complexArgumentDefined z <;> simp [complexArgument, hz]

theorem complexPhase_eq_none_iff (z : ℂ) :
    complexPhase z = none ↔ ¬ complexArgumentDefined z := by
  by_cases hz : complexArgumentDefined z <;> simp [complexPhase, complexArgument, hz]

theorem complexArgument_eq_some_iff {z : ℂ} {θ : ℝ} :
    complexArgument z = some θ ↔
      complexArgumentDefined z ∧ complexPrincipalArgument z = θ := by
  by_cases hz : complexArgumentDefined z <;> simp [complexArgument, hz]

theorem complexRadius_nonneg (z : ℂ) :
    0 ≤ complexRadius z := by
  simpa [complexRadius, complex_abs] using norm_nonneg z

theorem complexOfPolar_eq_mul_exp (r θ : ℝ) :
    complexOfPolar r θ = (r : ℂ) * Complex.exp (θ * Complex.I) := by
  apply Complex.ext <;>
    simp [complexOfPolar, Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      mul_add]

theorem complexOfPolar_periodic_two_pi (r θ : ℝ) :
    complexOfPolar r (θ + 2 * Real.pi) = complexOfPolar r θ := by
  apply Complex.ext <;> simp [complexOfPolar, Real.sin_add, Real.cos_add]

theorem complexOfPolar_mul (r₁ θ₁ r₂ θ₂ : ℝ) :
    complexOfPolar r₁ θ₁ * complexOfPolar r₂ θ₂ =
      complexOfPolar (r₁ * r₂) (θ₁ + θ₂) := by
  apply Complex.ext
  · simp [complexOfPolar, Real.cos_add, Real.sin_add, sub_eq_add_neg, mul_add,
      mul_left_comm, mul_comm]
    ring
  · simp [complexOfPolar, Real.cos_add, Real.sin_add, sub_eq_add_neg, mul_add,
      mul_left_comm, mul_comm]
    ring

theorem complexOfPolar_radius_principalArgument {z : ℂ}
    (hz : complexArgumentDefined z) :
    complexOfPolar (complexRadius z) (complexPrincipalArgument z) = z := by
  rw [complexOfPolar_eq_mul_exp]
  simpa [complexRadius, complex_abs, complexPrincipalArgument] using
    Complex.norm_mul_exp_arg_mul_I z

theorem complexOfPolar_of_argument_eq_some {z : ℂ} {θ : ℝ}
    (hθ : complexArgument z = some θ) :
    complexOfPolar (complexRadius z) θ = z := by
  rcases complexArgument_eq_some_iff.mp hθ with ⟨hz, harg⟩
  subst θ
  exact complexOfPolar_radius_principalArgument hz

theorem complexOfPolar_RV_of_argument_eq_some
    {Ω : Type*} {Z : Ω → ℂ} {ω : Ω} {θ : ℝ}
    (hθ : complexArgument (Z ω) = some θ) :
    complexOfPolar (complexRadius (Z ω)) θ = Z ω := by
  exact complexOfPolar_of_argument_eq_some hθ

theorem complexPolarRV_radius_nonneg
    {Ω : Type*} (Z : Ω → ℂ) (ω : Ω) :
    0 ≤ (complexPolarRV Z ω).1 := by
  simpa [complexPolarRV, complexPolarData] using complexRadius_nonneg (Z ω)

theorem complexPolarRV_reconstruct_of_argument_eq_some
    {Ω : Type*} (Z : Ω → ℂ) {ω : Ω} {θ : ℝ}
    (hθ : (complexPolarRV Z ω).2 = some θ) :
    complexOfPolar (complexPolarRV Z ω).1 θ = Z ω := by
  have hθ' : complexArgument (Z ω) = some θ := by
    simpa [complexPolarRV, complexPolarData] using hθ
  simpa [complexPolarRV, complexPolarData] using
    (complexOfPolar_RV_of_argument_eq_some (Z := Z) (ω := ω) hθ')

theorem complexPhaseRV_some_of_argument_eq_some
    {Ω : Type*} {Z : Ω → ℂ} {ω : Ω} {θ : ℝ}
    (hθ : complexArgument (Z ω) = some θ) :
    complexPhaseRV Z ω = some (θ : Real.Angle) := by
  simp [complexPhaseRV, complexPhase, hθ]

theorem def_4_4_polar_form :
    complexArgument 0 = none ∧
    complexPhase 0 = none ∧
    (∀ z : ℂ, 0 ≤ complexRadius z) ∧
    (∀ z : ℂ, complexArgumentDefined z →
      complexArgument z = some (complexPrincipalArgument z) ∧
      complexPhase z = some (complexPrincipalArgument z : Real.Angle) ∧
      complexOfPolar (complexRadius z) (complexPrincipalArgument z) = z) ∧
    (∀ r θ : ℝ,
      complexOfPolar r (θ + 2 * Real.pi) = complexOfPolar r θ) ∧
    (∀ r₁ θ₁ r₂ θ₂ : ℝ,
      complexOfPolar r₁ θ₁ * complexOfPolar r₂ θ₂ =
        complexOfPolar (r₁ * r₂) (θ₁ + θ₂)) ∧
    (∀ {Ω : Type*} (Z : Ω → ℂ) (ω : Ω) (θ : ℝ),
      complexArgument (Z ω) = some θ →
      complexOfPolar (complexRadius (Z ω)) θ = Z ω) := by
  refine ⟨complexArgument_undefined_at_zero, complexPhase_undefined_at_zero,
    complexRadius_nonneg, ?_, complexOfPolar_periodic_two_pi, complexOfPolar_mul, ?_⟩
  · intro z hz
    exact ⟨complexArgument_some_of_defined hz, complexPhase_some_of_defined hz,
      complexOfPolar_radius_principalArgument hz⟩
  · intro Ω Z ω θ hθ
    exact complexOfPolar_RV_of_argument_eq_some hθ
