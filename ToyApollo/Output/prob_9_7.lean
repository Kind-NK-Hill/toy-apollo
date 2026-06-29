/-
TASK ID: prob_9_7
TYPE: Problem
SOURCE PLAN: chapter9-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_9_3

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

def IsSymmetricCharacteristicLaw (μ : Measure ℝ) : Prop :=
  μ.map (fun x : ℝ => -x) = μ

def IsSymmetricRandomVariable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ) : Prop :=
  IsSymmetricCharacteristicLaw (P.map Z)

def CharacteristicFunctionIsRealValued (φ : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, star (φ t) = φ t

theorem prob97_charFun_reflectedMeasure_eq_star
    (μ : Measure ℝ) (t : ℝ) :
    charFun (μ.map (fun x : ℝ => -x)) t = star (charFun μ t) := by
  calc
    charFun (μ.map (fun x : ℝ => -x)) t = charFun μ ((-1 : ℝ) * t) := by
      simpa using (charFun_map_mul (μ := μ) (-1 : ℝ) t)
    _ = charFun μ (-t) := by simp
    _ = star (charFun μ t) := by
      simpa using (charFun_neg (μ := μ) t)

theorem symmetricLaw_charFun_realValued
    (μ : Measure ℝ) (hμ : IsSymmetricCharacteristicLaw μ) :
    CharacteristicFunctionIsRealValued (charFun μ) := by
  intro t
  have h : charFun μ t = star (charFun μ t) := by
    calc
      charFun μ t = charFun (μ.map (fun x : ℝ => -x)) t := by
        rw [hμ]
      _ = star (charFun μ t) := prob97_charFun_reflectedMeasure_eq_star μ t
  exact h.symm

theorem symmetricRandomVariable_characteristicFunction_realValued
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ : AEMeasurable Z P)
    (hSymm : IsSymmetricRandomVariable P Z) :
    CharacteristicFunctionIsRealValued (characteristicFunction P Z) := by
  haveI : IsProbabilityMeasure (P.map Z) := Measure.isProbabilityMeasure_map hZ
  intro t
  rw [characteristicFunction_law_eq_charFun (μ := P) (X := Z) hZ t]
  exact symmetricLaw_charFun_realValued (P.map Z) hSymm t

noncomputable def iidDifferenceLaw (μ : Measure ℝ) : Measure ℝ :=
  μ ∗ μ.map (fun x : ℝ => -x)

theorem iidDifferenceLaw_charFun
    (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    charFun (iidDifferenceLaw μ) t = charFun μ t * star (charFun μ t) := by
  unfold iidDifferenceLaw
  rw [characteristicFunction_convolution_product]
  rw [prob97_charFun_reflectedMeasure_eq_star]

theorem iidDifferenceLaw_symmetric
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsSymmetricCharacteristicLaw (iidDifferenceLaw μ) := by
  haveI : IsProbabilityMeasure (μ.map (fun x : ℝ => -x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (iidDifferenceLaw μ) := by
    unfold iidDifferenceLaw
    infer_instance
  apply Measure.ext_of_charFun
  funext t
  calc
    charFun ((iidDifferenceLaw μ).map (fun x : ℝ => -x)) t =
        star (charFun (iidDifferenceLaw μ) t) := by
      exact prob97_charFun_reflectedMeasure_eq_star (iidDifferenceLaw μ) t
    _ = star (charFun μ t * star (charFun μ t)) := by
      rw [iidDifferenceLaw_charFun]
    _ = charFun μ t * star (charFun μ t) := by
      simp [star_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = charFun (iidDifferenceLaw μ) t := by
      rw [iidDifferenceLaw_charFun]

theorem iid_difference_law_eq_iidDifferenceLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXY : X ⟂ᵢ[P] Y) (hIdent : P.map X = P.map Y) :
    P.map (fun ω => X ω - Y ω) = iidDifferenceLaw (P.map X) := by
  have hNegY : AEMeasurable (fun ω => -Y ω) P := hY.neg
  have hXNegY : X ⟂ᵢ[P] (fun ω => -Y ω) := by
    simpa [Function.comp_def] using
      (hXY.comp (φ := fun x : ℝ => x) (ψ := fun y : ℝ => -y)
        measurable_id measurable_neg)
  have hConv :
      P.map (fun ω => X ω + -Y ω) =
        (P.map X) ∗ (P.map (fun ω => -Y ω)) :=
    hXNegY.map_add_eq_map_conv_map₀ hX hNegY
  have hMapNegY :
      P.map (fun ω => -Y ω) = (P.map Y).map (fun y : ℝ => -y) := by
    rw [show (fun ω => -Y ω) = (fun y : ℝ => -y) ∘ Y from rfl]
    rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) hY]
  calc
    P.map (fun ω => X ω - Y ω) = P.map (fun ω => X ω + -Y ω) := by
      simp [sub_eq_add_neg]
    _ = (P.map X) ∗ (P.map (fun ω => -Y ω)) := hConv
    _ = (P.map X) ∗ ((P.map X).map (fun y : ℝ => -y)) := by
      rw [hMapNegY, ← hIdent]
    _ = iidDifferenceLaw (P.map X) := rfl

theorem iid_difference_symmetric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXY : X ⟂ᵢ[P] Y) (hIdent : P.map X = P.map Y) :
    IsSymmetricCharacteristicLaw (P.map (fun ω => X ω - Y ω)) := by
  rw [iid_difference_law_eq_iidDifferenceLaw hX hY hXY hIdent]
  haveI : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hX
  exact iidDifferenceLaw_symmetric (P.map X)

theorem prob_9_7
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z X Y : Ω → ℝ}
    (hZ : AEMeasurable Z P) (hSymmZ : IsSymmetricRandomVariable P Z)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hXY : X ⟂ᵢ[P] Y) (hIdent : P.map X = P.map Y) :
    CharacteristicFunctionIsRealValued (characteristicFunction P Z) ∧
      IsSymmetricCharacteristicLaw (P.map (fun ω => X ω - Y ω)) :=
  ⟨symmetricRandomVariable_characteristicFunction_realValued hZ hSymmZ,
    iid_difference_symmetric hX hY hXY hIdent⟩
