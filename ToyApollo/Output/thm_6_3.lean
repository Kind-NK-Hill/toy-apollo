/-
TASK ID: thm_6_3
TYPE: Theorem_with_Proof
SOURCE PLAN: 20_chap6_nonnegative_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

-- Source Definition 6.3: simple ENNReal functions lying below the target function.
-- Nonnegativity is encoded by the codomain `ENNReal`; simplicity by `SimpleFunc`.
def sourceSimpleApproximationSet (X : Ω → ENNReal) : Set (SimpleFunc Ω ENNReal) :=
  {f | ∀ ω, f ω ≤ X ω}

noncomputable def sourceSimpleApproximationIntegral
    (μ : Measure Ω) (f : SimpleFunc Ω ENNReal) : ENNReal :=
  f.lintegral μ

noncomputable def sourceSupIntegral (μ : Measure Ω) (X : Ω → ENNReal) : ENNReal :=
  ⨆ f : sourceSimpleApproximationSet X, sourceSimpleApproximationIntegral μ f.1

lemma sourceSimpleApproximationSet_mono {X Y : Ω → ENNReal} (hXY : X ≤ Y) :
    sourceSimpleApproximationSet X ⊆ sourceSimpleApproximationSet Y := by
  intro f hf ω
  exact le_trans (hf ω) (hXY ω)

lemma sourceSupIntegral_mono (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hsub : sourceSimpleApproximationSet X ⊆ sourceSimpleApproximationSet Y) :
    sourceSupIntegral μ X ≤ sourceSupIntegral μ Y := by
  unfold sourceSupIntegral
  refine iSup_le ?_
  intro f
  exact le_iSup
    (fun g : sourceSimpleApproximationSet Y =>
      sourceSimpleApproximationIntegral μ g.1)
    ⟨f.1, hsub f.2⟩

lemma sourceSupIntegral_eq_lintegral (μ : Measure Ω) (X : Ω → ENNReal) :
    sourceSupIntegral μ X = ∫⁻ ω, X ω ∂μ := by
  unfold sourceSupIntegral sourceSimpleApproximationIntegral sourceSimpleApproximationSet
  rw [MeasureTheory.lintegral]
  exact (iSup_subtype'
    (α := ENNReal)
    (ι := SimpleFunc Ω ENNReal)
    (p := fun f => ∀ ω, f ω ≤ X ω)
    (f := fun f _ => f.lintegral μ)).symm

theorem thm_6_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hXY : X ≤ Y) :
    ∫⁻ ω, X ω ∂μ ≤ ∫⁻ ω, Y ω ∂μ := by
  rw [← sourceSupIntegral_eq_lintegral μ X, ← sourceSupIntegral_eq_lintegral μ Y]
  exact sourceSupIntegral_mono μ (sourceSimpleApproximationSet_mono hXY)
