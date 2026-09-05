/-
TASK ID: thm_13_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-properties
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_3
import ProbabilityTheory.chapter_13.thm_13_4
import ProbabilityTheory.chapter_13.thm_13_6




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section



theorem thm_13_7_of_stronglyMeasurable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X : Ω → ℝ}
    (hXm : StronglyMeasurable[𝓖] X) (hXi : Integrable X P) :
    P[X | 𝓖] = X :=
  condExp_of_stronglyMeasurable h𝓖 hXm hXi



theorem thm_13_7_of_GMeasurable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (h𝓖 : IsSubSigmaField 𝓖 𝓕)
    [SigmaFinite (P.trim h𝓖)] {X : Ω → ℝ}
    (hXm : GMeasurable 𝓖 X) (hXi : Integrable X P) :
    P[X | 𝓖] = X :=
  have hXsm : StronglyMeasurable[𝓖] X :=
    (show Measurable[𝓖] X from hXm).stronglyMeasurable
  @thm_13_7_of_stronglyMeasurable Ω 𝓕 P 𝓖 h𝓖 _ X hXsm hXi

 
theorem thm_13_7_const {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) (c : ℝ) :
    P[fun _ : Ω => c | 𝓖] = fun _ => c :=
  condExp_const h𝓖 c



theorem thm_13_7_nonneg {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X : Ω → ℝ}
    (hX : 0 ≤ᵐ[P] X) :
    0 ≤ᵐ[P] P[X | 𝓖] :=
  condExp_nonneg hX

 
theorem thm_13_7_add {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X Y : Ω → ℝ}
    (hX : Integrable X P) (hY : Integrable Y P) :
    P[X + Y | 𝓖] =ᵐ[P] P[X | 𝓖] + P[Y | 𝓖] :=
  condExp_add hX hY 𝓖

 
theorem thm_13_7_smul {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} (a : ℝ) (X : Ω → ℝ) :
    P[a • X | 𝓖] =ᵐ[P] a • P[X | 𝓖] :=
  condExp_smul a X 𝓖

 
theorem thm_13_7_mono {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X Y : Ω → ℝ}
    (hX : Integrable X P) (hY : Integrable Y P) (hXY : X ≤ᵐ[P] Y) :
    P[X | 𝓖] ≤ᵐ[P] P[Y | 𝓖] :=
  condExp_mono hX hY hXY

 
theorem thm_13_7_abs_le {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {X : Ω → ℝ}
    (hX : Integrable X P) :
    (fun ω => |P[X | 𝓖] ω|) ≤ᵐ[P] P[fun ω => |X ω| | 𝓖] := by
  filter_upwards
    [condExp_mono hX hX.abs (ae_of_all P fun ω => le_abs_self (X ω)),
      (condExp_neg (μ := P) (f := X) (m := 𝓖)).symm.le.trans
        (condExp_mono hX.neg hX.abs (ae_of_all P fun ω => neg_le_abs (X ω))),
      condExp_nonneg (μ := P) (m := 𝓖)
        (ae_of_all P fun ω => abs_nonneg (X ω))]
    with ω hpos hneg hright
  simpa [abs_of_nonneg hright] using abs_le_abs hpos hneg



theorem thm_13_7 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    (h𝓖 : IsSubSigmaField 𝓖 𝓕) [SigmaFinite (P.trim h𝓖)] :
    (∀ X : Ω → ℝ, GMeasurable 𝓖 X → Integrable X P →
        P[X | 𝓖] = X) ∧
      (∀ c : ℝ, P[fun _ : Ω => c | 𝓖] = fun _ => c) ∧
      (∀ X : Ω → ℝ, 0 ≤ᵐ[P] X → 0 ≤ᵐ[P] P[X | 𝓖]) ∧
      (∀ X Y : Ω → ℝ, Integrable X P → Integrable Y P →
        P[X + Y | 𝓖] =ᵐ[P] P[X | 𝓖] + P[Y | 𝓖]) ∧
      (∀ (a : ℝ) (X : Ω → ℝ), P[a • X | 𝓖] =ᵐ[P] a • P[X | 𝓖]) ∧
      (∀ X Y : Ω → ℝ, Integrable X P → Integrable Y P → X ≤ᵐ[P] Y →
        P[X | 𝓖] ≤ᵐ[P] P[Y | 𝓖]) ∧
      (∀ X : Ω → ℝ, Integrable X P →
        (fun ω => |P[X | 𝓖] ω|) ≤ᵐ[P] P[fun ω => |X ω| | 𝓖]) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X hXm hXi
    exact @thm_13_7_of_GMeasurable Ω 𝓕 P 𝓖 h𝓖 _ X hXm hXi
  · intro c
    exact @thm_13_7_const Ω 𝓕 P _ 𝓖 h𝓖 c
  · intro X hX
    exact @thm_13_7_nonneg Ω 𝓕 P 𝓖 X hX
  · intro X Y hX hY
    exact @thm_13_7_add Ω 𝓕 P 𝓖 X Y hX hY
  · intro a X
    exact @thm_13_7_smul Ω 𝓕 P 𝓖 a X
  · intro X Y hX hY hXY
    exact @thm_13_7_mono Ω 𝓕 P 𝓖 X Y hX hY hXY
  · intro X hX
    exact @thm_13_7_abs_le Ω 𝓕 P 𝓖 X hX
