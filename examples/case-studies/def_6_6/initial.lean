import Mathlib

/-!
Sanitized public Interface slice for case study `def_6_6`.
The private source excerpt and prompt-pack metadata are omitted.
-/

open MeasureTheory

namespace InitialDef66

noncomputable def posPart {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (X ω).toENNReal

noncomputable def negPart {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → EReal) : Ω → ENNReal :=
  fun ω => (-X ω).toENNReal

noncomputable def posLIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, posPart X ω ∂μ

noncomputable def negLIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EReal) : ENNReal :=
  ∫⁻ ω, negPart X ω ∂μ

/-- Initial gate: finite positive and negative parts, but no measurability. -/
def realIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EReal) : Prop :=
  posLIntegral μ X < ⊤ ∧ negLIntegral μ X < ⊤

/-- Initial public value: callable without a proof and totalized through `toReal`. -/
noncomputable def realValue {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → EReal) : ℝ :=
  (((posLIntegral μ X : EReal) - (negLIntegral μ X : EReal)).toReal)

def complexIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) : Prop :=
  realIntegrable μ (fun ω => ((Z ω).re : EReal)) ∧
    realIntegrable μ (fun ω => ((Z ω).im : EReal))

noncomputable def complexIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℂ) : Option ℂ := by
  classical
  exact
    if complexIntegrable μ Z then
      some
        (Complex.ofReal (realValue μ (fun ω => ((Z ω).re : EReal))) +
          Complex.I * Complex.ofReal (realValue μ (fun ω => ((Z ω).im : EReal))))
    else
      none

end InitialDef66
