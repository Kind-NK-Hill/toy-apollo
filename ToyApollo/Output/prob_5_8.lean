/-
TASK ID: prob_5_8
TYPE: Problem
SOURCE PLAN: 18_chap5_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable def standardNormal : Measure ℝ := gaussianReal 0 1

private lemma measurable_ite_coin {Ω : Type} [MeasurableSpace Ω]
    {Z : Ω → ℝ} {C : Ω → Bool} (hZ : Measurable Z) (hC : Measurable C) :
    Measurable (fun ω => if C ω then Z ω else (0 : ℝ)) := by
  exact Measurable.ite (hC (MeasurableSingletonClass.measurableSet_singleton _)) hZ measurable_const

private lemma measurable_ite_coin' {Ω : Type} [MeasurableSpace Ω]
    {Z : Ω → ℝ} {C : Ω → Bool} (hZ : Measurable Z) (hC : Measurable C) :
    Measurable (fun ω => if C ω then (0 : ℝ) else Z ω) := by
  refine' Measurable.ite _ measurable_const hZ
  exact hC (MeasurableSingletonClass.measurableSet_singleton _)

private lemma map_X_eq_map_Y {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} {C : Ω → Bool}
    (hZ : Measurable Z) (hC : Measurable C)
    (hC_fair : ∀ b, P {ω | C ω = b} = (1 / 2 : ℝ≥0∞))
    (h_indep : IndepFun Z C P) :
    P.map (fun ω => if C ω then Z ω else 0) =
      P.map (fun ω => if C ω then (0 : ℝ) else Z ω) := by
  ext s hs
  by_cases hs0 : 0 ∈ s <;> simp_all +decide [Set.indicator]
  · rw [Measure.map_apply, Measure.map_apply] <;> norm_num [hs, hs0, hZ, hC]
    · rw [
        show (fun ω => if C ω = true then Z ω else 0) ⁻¹' s =
          ({ω | C ω = true} ∩ {ω | Z ω ∈ s}) ∪
          ({ω | C ω = false} ∩ {ω | 0 ∈ s}) from ?_,
        show (fun ω => if C ω = true then 0 else Z ω) ⁻¹' s =
          ({ω | C ω = true} ∩ {ω | 0 ∈ s}) ∪
          ({ω | C ω = false} ∩ {ω | Z ω ∈ s}) from ?_]
      · rw [MeasureTheory.measure_union, MeasureTheory.measure_union] <;>
          norm_num [hs0, hC_fair]
        · rw [add_comm, ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at *
          have := h_indep s {true} hs (by norm_num)
          have := h_indep s {false} hs (by norm_num)
          simp_all +decide [Set.inter_comm]
          simp_all +decide [Set.inter_comm, Set.preimage]
        · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by aesop
        · exact MeasurableSet.inter
            (hC (MeasurableSingletonClass.measurableSet_singleton _)) (hZ hs)
        · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => by aesop
        · exact MeasurableSet.mem (hC (MeasurableSingletonClass.measurableSet_singleton _))
      · ext ω
        by_cases h : C ω <;> aesop
      · ext ω
        by_cases h : C ω <;> simp +decide [h, hs0]
    · exact Measurable.ite
        (hC (MeasurableSingletonClass.measurableSet_singleton _)) measurable_const hZ
    · exact Measurable.ite
        (hC (MeasurableSingletonClass.measurableSet_singleton _)) hZ measurable_const
  · rw [MeasureTheory.Measure.map_apply_of_aemeasurable,
      MeasureTheory.Measure.map_apply_of_aemeasurable] <;> norm_num [*]
    · rw [
        show (fun ω => if C ω = true then Z ω else 0) ⁻¹' s =
          ({ω | C ω = true} ∩ Z ⁻¹' s) from ?_,
        show (fun ω => if C ω = true then 0 else Z ω) ⁻¹' s =
          ({ω | C ω = false} ∩ Z ⁻¹' s) from ?_]
      · rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at h_indep
        simp_all +decide [Set.inter_comm, Set.preimage]
        have := h_indep s {Bool.true} hs
        have := h_indep s {Bool.false} hs
        aesop
      · grind
      · ext ω
        by_cases h : C ω <;> aesop
    · exact Measurable.aemeasurable (by
        exact Measurable.ite
          (hC (MeasurableSingletonClass.measurableSet_singleton _)) measurable_const hZ)
    · exact Measurable.aemeasurable (by
        exact Measurable.ite
          (hC (MeasurableSingletonClass.measurableSet_singleton _)) hZ measurable_const)

private lemma not_indep_X_Y {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} {C : Ω → Bool}
    (hZ : Measurable Z) (hC : Measurable C)
    (hZ_std : P.map Z = standardNormal)
    (hC_fair : ∀ b, P {ω | C ω = b} = (1 / 2 : ℝ≥0∞))
    (h_indep : IndepFun Z C P) :
    ¬ IndepFun (fun ω => if C ω then Z ω else (0 : ℝ))
        (fun ω => if C ω then (0 : ℝ) else Z ω) P := by
  intro h_ind
  have h_pos :
      (P {ω | (if C ω then Z ω else 0) > 0}) > 0 ∧
        (P {ω | (if C ω then 0 else Z ω) > 0}) > 0 := by
    have h_pos :
        (P {ω | Z ω > 0 ∧ C ω}) > 0 ∧
          (P {ω | Z ω > 0 ∧ ¬ C ω}) > 0 := by
      have h_pos : (P {ω | Z ω > 0}) > 0 := by
        have h_std_normal_pos : (standardNormal (Set.Ioi 0)) > 0 := by
          unfold standardNormal
          norm_num [gaussianReal]
          rw [MeasureTheory.lintegral_pos_iff_support]
          · simp +decide [Function.support, gaussianPDF]
            norm_num [gaussianPDFReal]
            exact lt_of_lt_of_le
              (by norm_num [Real.sqrt_pos, Real.pi_pos])
              (MeasureTheory.measure_mono <|
                show Set.Ioi 0 ⊆
                    {x : ℝ |
                      0 < (Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹ *
                        Real.exp (-x ^ 2 / 2)} ∩ Ioi 0 from
                  fun x hx => ⟨by exact Set.mem_setOf.mpr <| by positivity, hx⟩)
          · fun_prop
        rw [← hZ_std, MeasureTheory.Measure.map_apply] at h_std_normal_pos <;> aesop
      have h_pos :
          (P {ω | Z ω > 0 ∧ C ω}) = (P {ω | Z ω > 0}) * (P {ω | C ω}) ∧
            (P {ω | Z ω > 0 ∧ ¬ C ω}) = (P {ω | Z ω > 0}) * (P {ω | ¬ C ω}) := by
        constructor <;> rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at h_indep
        · change
            P (Z ⁻¹' Set.Ioi 0 ∩ C ⁻¹' ({true} : Set Bool)) =
              P (Z ⁻¹' Set.Ioi 0) * P (C ⁻¹' ({true} : Set Bool))
          exact h_indep (Set.Ioi 0) {true} measurableSet_Ioi (by norm_num)
        · change
            P (Z ⁻¹' Set.Ioi 0 ∩ C ⁻¹' {b : Bool | ¬ b = true}) =
              P (Z ⁻¹' Set.Ioi 0) * P (C ⁻¹' {b : Bool | ¬ b = true})
          exact h_indep (Set.Ioi 0) {b : Bool | ¬ b = true}
            measurableSet_Ioi (by norm_num)
      aesop
    convert h_pos using 3 <;> aesop
  have h_zero :
      P {ω |
        (if C ω then Z ω else 0) > 0 ∧
          (if C ω then 0 else Z ω) > 0} = 0 := by
    exact MeasureTheory.measure_mono_null (fun x hx => by aesop) MeasureTheory.measure_empty
  have := h_ind.measure_inter_preimage_eq_mul
  specialize this (Set.Ioi 0) (Set.Ioi 0)
  simp_all +decide [Set.preimage]
  exact absurd this (by
    rw [
      show {x : Ω | 0 < if C x = true then Z x else 0} ∩
          {x : Ω | 0 < if C x = true then 0 else Z x} =
          {x : Ω |
            (0 < if C x = true then Z x else 0) ∧
              0 < if C x = true then 0 else Z x} by rfl]
    rw [h_zero]
    exact ne_of_lt (ENNReal.mul_pos h_pos.1.ne' h_pos.2.ne'))

private lemma joint_cdf_XY {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} {C : Ω → Bool}
    (hZ : Measurable Z) (hC : Measurable C)
    (hC_fair : ∀ b, P {ω | C ω = b} = (1 / 2 : ℝ≥0∞))
    (h_indep : IndepFun Z C P) (x y : ℝ) :
    P {ω | (if C ω then Z ω else (0 : ℝ)) ≤ x ∧
        (if C ω then (0 : ℝ) else Z ω) ≤ y} =
      (1 / 2 : ℝ≥0∞) * (if 0 ≤ y then (P.map Z) (Iic x) else 0) +
      (1 / 2 : ℝ≥0∞) * (if 0 ≤ x then (P.map Z) (Iic y) else 0) := by
  have h_split :
      P {ω | (if C ω then Z ω else 0) ≤ x ∧ (if C ω then 0 else Z ω) ≤ y} =
        P ({ω | C ω = true} ∩ {ω | Z ω ≤ x ∧ 0 ≤ y}) +
        P ({ω | C ω = false} ∩ {ω | 0 ≤ x ∧ Z ω ≤ y}) := by
    rw [← MeasureTheory.measure_union]
    · exact congr_arg _ (by ext ω; by_cases h : C ω <;> aesop)
    · grind +qlia
    · by_cases hx : 0 ≤ x <;> simp +decide [hx]
      exact MeasurableSet.inter
        (hC (MeasurableSingletonClass.measurableSet_singleton _)) (hZ measurableSet_Iic)
  have h_split :
      P ({ω | C ω = true} ∩ {ω | Z ω ≤ x ∧ 0 ≤ y}) =
          P {ω | C ω = true} * P {ω | Z ω ≤ x ∧ 0 ≤ y} ∧
        P ({ω | C ω = false} ∩ {ω | 0 ≤ x ∧ Z ω ≤ y}) =
          P {ω | C ω = false} * P {ω | 0 ≤ x ∧ Z ω ≤ y} := by
    constructor <;> rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at h_indep
    · convert h_indep {z : ℝ | z ≤ x ∧ 0 ≤ y} {true} _ _ using 1 <;>
        norm_num [Set.preimage]
      · rw [Set.inter_comm]
      · ring
      · exact Measurable.and measurableSet_Iic.mem measurable_const
    · convert h_indep ({z : ℝ | 0 ≤ x ∧ z ≤ y}) {false} _ _ using 1 <;>
        norm_num [Set.preimage]
      · rw [Set.inter_comm]
      · ring
      · exact Measurable.and measurable_const measurableSet_Iic.mem
  split_ifs <;> simp_all +decide [Set.setOf_and]
  · rfl
  · rfl
  · rfl

private lemma joint_cdf_XZ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℝ} {C : Ω → Bool}
    (hZ : Measurable Z) (hC : Measurable C)
    (hC_fair : ∀ b, P {ω | C ω = b} = (1 / 2 : ℝ≥0∞))
    (h_indep : IndepFun Z C P) (x z : ℝ) :
    P {ω | (if C ω then Z ω else (0 : ℝ)) ≤ x ∧ Z ω ≤ z} =
      (1 / 2 : ℝ≥0∞) * (P.map Z) (Iic (min x z)) +
      (1 / 2 : ℝ≥0∞) * (if 0 ≤ x then (P.map Z) (Iic z) else 0) := by
  have h_case1 :
      P {ω | C ω = true ∧ Z ω ≤ min x z} =
        (1 / 2 : ℝ≥0∞) * (P.map Z) (Iic (min x z)) := by
    have := h_indep
    rw [← hC_fair true, ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at *
    convert this (Iic (min x z)) {Bool.true} measurableSet_Iic
      (MeasurableSingletonClass.measurableSet_singleton _) using 1
    simp +decide [Set.preimage]
    · exact congr_arg _ (by ext; aesop)
    · rw [mul_comm, Measure.map_apply] <;> aesop
  have h_case2 :
      P {ω | C ω = false ∧ 0 ≤ x ∧ Z ω ≤ z} =
        (if 0 ≤ x then (1 / 2 : ℝ≥0∞) * (P.map Z) (Iic z) else 0) := by
    by_cases hx : 0 ≤ x <;> simp +decide [hx]
    have h_case2 :
        P {ω | C ω = false ∧ Z ω ≤ z} =
          P {ω | C ω = false} * P {ω | Z ω ≤ z} := by
      have := h_indep.symm
      rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at this
      change
        P (C ⁻¹' ({false} : Set Bool) ∩ Z ⁻¹' Set.Iic z) =
          P (C ⁻¹' ({false} : Set Bool)) * P (Z ⁻¹' Set.Iic z)
      exact this {false} (Set.Iic z) (by norm_num) measurableSet_Iic
    rw [h_case2, hC_fair, Measure.map_apply] <;> aesop
  convert congr_arg₂ (· + ·) h_case1 h_case2 using 1
  · rw [← MeasureTheory.measure_union]
    · congr with ω
      by_cases h : C ω <;> simp +decide [h]
      · exact ⟨fun h' => Or.inl ⟨h, h'⟩, fun h' => by cases h' <;> aesop⟩
      · exact
          ⟨fun h' => Or.inr ⟨by simpa using h, h'.1, h'.2⟩,
            fun h' => by cases h' <;> aesop⟩
    · exact Set.disjoint_left.mpr fun ω hω₁ hω₂ => by aesop
    · by_cases hx : 0 ≤ x <;> simp +decide [hx]
      exact MeasurableSet.mem
        (MeasurableSet.inter (hC (MeasurableSingletonClass.measurableSet_singleton _))
          (hZ measurableSet_Iic))
  · split_ifs <;> ring

theorem prob_5_8 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z) (hZ_std : P.map Z = standardNormal)
    (C : Ω → Bool) (hC_meas : Measurable C)
    (hC_fair : ∀ b, P {ω | C ω = b} = (1 / 2 : ℝ≥0∞))
    (h_indep : IndepFun Z C P) :
    let X : Ω → ℝ := fun ω => if C ω then Z ω else 0
    let Y : Ω → ℝ := fun ω => if C ω then 0 else Z ω
    Measurable X ∧ Measurable Y ∧
    (P.map X = P.map Y) ∧
    (¬ IndepFun X Y P) ∧
    (∀ x y, P {ω | X ω ≤ x ∧ Y ω ≤ y} =
      (1 / 2 : ℝ≥0∞) * (if 0 ≤ y then (P.map Z) (Iic x) else 0) +
      (1 / 2 : ℝ≥0∞) * (if 0 ≤ x then (P.map Z) (Iic y) else 0)) ∧
    (∀ x z, P {ω | X ω ≤ x ∧ Z ω ≤ z} =
      (1 / 2 : ℝ≥0∞) * (P.map Z) (Iic (min x z)) +
      (1 / 2 : ℝ≥0∞) * (if 0 ≤ x then (P.map Z) (Iic z) else 0)) := by
  refine ⟨measurable_ite_coin hZ_meas hC_meas,
         measurable_ite_coin' hZ_meas hC_meas,
         map_X_eq_map_Y hZ_meas hC_meas hC_fair h_indep,
         not_indep_X_Y hZ_meas hC_meas hZ_std hC_fair h_indep,
         joint_cdf_XY hZ_meas hC_meas hC_fair h_indep,
         joint_cdf_XZ hZ_meas hC_meas hC_fair h_indep⟩
