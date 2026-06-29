/-
TASK ID: def_6_5
TYPE: Definition
SOURCE PLAN: 21_chap6_real_complex_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

namespace Def65Support

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

end Def65Support

noncomputable def textbookIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → EReal) : Option EReal :=
  if hUndefined :
      Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤ then
    none
  else
    let p := Def65Support.posLIntegral μ X
    let n := Def65Support.negLIntegral μ X
    some ((p : EReal) - (n : EReal))

def textbookIntegrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal) :
    Prop :=
  Def65Support.posLIntegral μ X < ⊤ ∧ Def65Support.negLIntegral μ X < ⊤

noncomputable def def_6_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → EReal) :
    Option EReal :=
  textbookIntegral μ X

noncomputable def textbookIntegralOn {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (s : Set Ω) (X : Ω → EReal) : Option EReal :=
  textbookIntegral μ (s.indicator X)

section TextbookIntegralLemmas

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → EReal}

theorem textbookIntegral_eq_none_iff :
    textbookIntegral μ X = none ↔
      Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤ := by
  unfold textbookIntegral
  by_cases hUndefined :
      Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤
  · simp [hUndefined]
  · simp [hUndefined]

theorem textbookIntegrable_pos_ne_top (hX : textbookIntegrable μ X) :
    Def65Support.posLIntegral μ X ≠ ⊤ := by
  exact ne_of_lt hX.1

theorem textbookIntegrable_neg_ne_top (hX : textbookIntegrable μ X) :
    Def65Support.negLIntegral μ X ≠ ⊤ := by
  exact ne_of_lt hX.2

theorem textbookIntegrable_implies_some (hX : textbookIntegrable μ X) :
    ∃ v : EReal, textbookIntegral μ X = some v := by
  unfold textbookIntegral
  have hUndefined :
      ¬ (Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤) := by
    intro hBothTop
    exact (textbookIntegrable_pos_ne_top hX) hBothTop.1
  refine ⟨(Def65Support.posLIntegral μ X : EReal) - (Def65Support.negLIntegral μ X : EReal), ?_⟩
  simp [hUndefined]

theorem textbookIntegral_of_nonneg
    (hX : ∀ ω, 0 ≤ X ω)
    (hneg_zero :
      Def65Support.negLIntegral μ X = 0) :
    textbookIntegral μ X = some (Def65Support.posLIntegral μ X : EReal) := by
  unfold textbookIntegral
  have hUndefined :
      ¬ (Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤) := by
    intro hBothTop
    simpa [hneg_zero] using hBothTop.2
  simp [hUndefined, hneg_zero]

end TextbookIntegralLemmas
