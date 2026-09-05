/-
TASK ID: def_6_3
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic








open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]



def simpleApproximationSet (X : Ω → ENNReal)
    : Set (SimpleFunc Ω ENNReal) :=
  {f | ∀ ω, f ω ≤ X ω}




noncomputable def textbookIntegralNonnegative
    (μ : Measure Ω) (X : Ω → ENNReal) : ENNReal :=
  ⨆ (f : SimpleFunc Ω ENNReal) (_hf : f ∈ simpleApproximationSet X),
    f.lintegral μ



theorem textbookIntegralNonnegative_eq_top_of_unbounded
    {μ : Measure Ω} {X : Ω → ENNReal}
    (h :
      ∀ C : ENNReal, C < ⊤ →
        ∃ f : SimpleFunc Ω ENNReal,
          f ∈ simpleApproximationSet X ∧ C < f.lintegral μ) :
    textbookIntegralNonnegative μ X = ⊤ := by
  by_contra htop
  have hlt : textbookIntegralNonnegative μ X < ⊤ := by
    exact (lt_top_iff_ne_top).2 htop
  rcases h (textbookIntegralNonnegative μ X) hlt with ⟨f, hfS, hf_lt⟩
  have hf_le :
      f.lintegral μ ≤ textbookIntegralNonnegative μ X := by
    exact le_iSup_of_le f (le_iSup_of_le hfS le_rfl)
  exact not_lt_of_ge hf_le hf_lt




theorem textbookIntegralNonnegative_eq_lintegral
    (μ : Measure Ω) (X : Ω → ENNReal) :
    textbookIntegralNonnegative μ X = ∫⁻ ω, X ω ∂μ := by
  simp [
    textbookIntegralNonnegative,
    simpleApproximationSet,
    MeasureTheory.lintegral_def,
    Pi.le_def
  ]





noncomputable def def_6_3 (μ : Measure Ω) (X : Ω → ENNReal)
    : ENNReal :=
  ∫⁻ ω, X ω ∂μ
