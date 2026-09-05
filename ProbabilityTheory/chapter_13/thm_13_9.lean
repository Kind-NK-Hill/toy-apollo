/-
TASK ID: thm_13_9
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-properties
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_3
import ProbabilityTheory.chapter_13.def_13_4
import ProbabilityTheory.chapter_13.thm_13_4
import ProbabilityTheory.chapter_13.thm_13_6
import ProbabilityTheory.chapter_13.thm_13_7




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section



theorem thm_13_9_indicator {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (_h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim _h𝓖)] {A : Set Ω} {Y : Ω → ℝ}
    (hY : Integrable Y P) (hA : IsMeasurableIn 𝓖 A) :
    P[A.indicator Y | 𝓖] =ᵐ[P] A.indicator (P[Y | 𝓖]) :=
  condExp_indicator (μ := P) (m := 𝓖) (s := A) hY hA



theorem thm_13_9_pullout {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X Y : Ω → ℝ}
    (hX : GMeasurable 𝓖 X) (hXY : Integrable (X * Y) P)
    (hY : Integrable Y P) :
    P[X * Y | 𝓖] =ᵐ[P] X * P[Y | 𝓖] := by
  have hXsm : StronglyMeasurable[𝓖] X :=
    (show Measurable[𝓖] X from hX).stronglyMeasurable
  exact condExp_mul_of_stronglyMeasurable_left
    (μ := P) (m := 𝓖) (f := X) (g := Y) hXsm hXY hY



theorem thm_13_9 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X Y : Ω → ℝ}
    (hX : GMeasurable 𝓖 X) (hXY : Integrable (X * Y) P)
    (hY : Integrable Y P) :
    P[X * Y | 𝓖] =ᵐ[P] X * P[Y | 𝓖] :=
  @thm_13_9_pullout Ω 𝓕 P 𝓖 h𝓖 _ X Y hX hXY hY



theorem thm_13_9_function_of_observation {Ω S : Type*}
    [𝓕 : MeasurableSpace Ω] [MeasurableSpace S]
    {P : Measure Ω} {Z : Ω → S} {g : S → ℝ} {Y : Ω → ℝ}
    (hZ : Measurable Z) (hg : Measurable g)
    [SigmaFinite (P.trim (def_13_4_sigma_subSigma_of_measurable hZ))]
    (hXY : Integrable ((g ∘ Z) * Y) P) (hY : Integrable Y P) :
    P[(g ∘ Z) * Y | def_13_4_sigma Z] =ᵐ[P]
      (g ∘ Z) * P[Y | def_13_4_sigma Z] := by
  have hX : GMeasurable (def_13_4_sigma Z) (g ∘ Z) :=
    (show Measurable[def_13_4_sigma Z] (g ∘ Z) from
      hg.comp (comap_measurable Z))
  exact thm_13_9 (def_13_4_sigma_subSigma_of_measurable hZ) hX hXY hY
