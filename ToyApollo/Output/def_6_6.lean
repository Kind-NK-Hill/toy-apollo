/-
TASK ID: def_6_6
TYPE: Definition
SOURCE PLAN: 21_chap6_real_complex_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

namespace Def66RealSupport

noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (X ω).toENNReal

noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω] (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal

noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂μ

noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂μ

def textbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : Prop :=
  posLIntegral μ X < ⊤ ∧ negLIntegral μ X < ⊤

noncomputable def textbookValue {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : ℝ :=
  (((posLIntegral μ X : EReal) - (negLIntegral μ X : EReal)).toReal)

end Def66RealSupport

def complexTextbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Prop :=
  Def66RealSupport.textbookIntegrable μ (fun ω => ((Z ω).re : EReal)) ∧
    Def66RealSupport.textbookIntegrable μ (fun ω => ((Z ω).im : EReal))

noncomputable def complexTextbookIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Z : Ω → ℂ) : Option ℂ := by
  classical
  exact
    if hZ : complexTextbookIntegrable μ Z then
      some
        (Complex.ofReal
            (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).re : EReal))) +
          Complex.I *
            Complex.ofReal
              (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).im : EReal))))
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
  classical
  refine ⟨Complex.ofReal
      (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).re : EReal))) +
    Complex.I *
      Complex.ofReal
        (Def66RealSupport.textbookValue μ (fun ω => ((Z ω).im : EReal))), ?_⟩
  simp [complexTextbookIntegral, hZ]
