/-
TASK ID: prob_13_8
TYPE: Problem
SOURCE PLAN: chapter13-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_13_3
import ToyApollo.Output.thm_13_2

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section

structure Prob138GeneralizedBayesData where
  conditionalIntegralOnB : ℝ
  conditionalIntegralOnOmega : ℝ
  probBA : ℝ
  probA : ℝ
  probA_ne_zero : probA ≠ 0
  numerator_eq : conditionalIntegralOnB = probBA
  denominator_eq : conditionalIntegralOnOmega = probA

theorem prob_13_8_denominator_ne_zero (D : Prob138GeneralizedBayesData) :
    D.conditionalIntegralOnOmega ≠ 0 := by
  rw [D.denominator_eq]
  exact D.probA_ne_zero

theorem prob_13_8_generalized_bayes_from_integrals
    (D : Prob138GeneralizedBayesData) :
    D.conditionalIntegralOnB / D.conditionalIntegralOnOmega =
      D.probBA / D.probA := by
  rw [D.numerator_eq, D.denominator_eq]

theorem prob_13_8_indicator_integral_inter {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {A B : Set Ω} (hA : MeasurableSet A) :
    ∫ ω in B, A.indicator (fun _ => (1 : ℝ)) ω ∂P =
      (P (B ∩ A)).toReal := by
  calc
    ∫ ω in B, A.indicator (fun _ => (1 : ℝ)) ω ∂P =
        (P.restrict B).real A := by
      simpa using
        (integral_indicator_one (μ := P.restrict B) (s := A) hA)
    _ = P.real (A ∩ B) := by
      rw [measureReal_restrict_apply hA]
    _ = (P (B ∩ A)).toReal := by
      rw [Set.inter_comm, measureReal_def]

theorem prob_13_8_indicator_integral_univ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂P = (P A).toReal := by
  calc
    ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂P = P.real A := by
      simpa using (integral_indicator_one (μ := P) (s := A) hA)
    _ = (P A).toReal := by
      rw [measureReal_def]

theorem prob_13_8_conditional_expectation_integrals {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓖 : SigmaField Ω} {h𝓖 : IsSubSigmaField 𝓖 𝓕}
    {A B : Set Ω} {CP : Ω → ℝ}
    (hCP : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 (A.indicator (fun _ => (1 : ℝ))) CP)
    (hB : IsMeasurableIn 𝓖 B)
    (hA : @MeasurableSet Ω 𝓕 A) :
    (∫ ω in B, CP ω ∂P = (P (B ∩ A)).toReal) ∧
      (∫ ω, CP ω ∂P = (P A).toReal) := by
  have hnum_def :
      ∫ ω in B, CP ω ∂P =
        ∫ ω in B, A.indicator (fun _ => (1 : ℝ)) ω ∂P :=
    @def_13_3_set_integral_eq Ω 𝓕 P 𝓖 h𝓖
      (A.indicator (fun _ => (1 : ℝ))) CP hCP B hB
  have hnum :
      ∫ ω in B, CP ω ∂P = (P (B ∩ A)).toReal := by
    rw [hnum_def, @prob_13_8_indicator_integral_inter Ω 𝓕 P A B hA]
  have hUniv : IsMeasurableIn 𝓖 (Set.univ : Set Ω) := by
    exact MeasurableSet.univ
  have hden_def :
      ∫ ω in (Set.univ : Set Ω), CP ω ∂P =
        ∫ ω in (Set.univ : Set Ω),
          A.indicator (fun _ => (1 : ℝ)) ω ∂P :=
    @def_13_3_set_integral_eq Ω 𝓕 P 𝓖 h𝓖
      (A.indicator (fun _ => (1 : ℝ))) CP hCP Set.univ hUniv
  have hden :
      ∫ ω, CP ω ∂P = (P A).toReal := by
    rw [← setIntegral_univ, hden_def, setIntegral_univ]
    exact @prob_13_8_indicator_integral_univ Ω 𝓕 P A hA
  exact ⟨hnum, hden⟩

theorem prob_13_8_generalized_bayes {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓖 : SigmaField Ω} {h𝓖 : IsSubSigmaField 𝓖 𝓕}
    {A B : Set Ω} {CP : Ω → ℝ}
    (hCP : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 (A.indicator (fun _ => (1 : ℝ))) CP)
    (hB : IsMeasurableIn 𝓖 B)
    (hA : @MeasurableSet Ω 𝓕 A)
    (hprobA : (P A).toReal ≠ 0) :
    (∫ ω in B, CP ω ∂P) / (∫ ω, CP ω ∂P) =
      (P (B ∩ A)).toReal / (P A).toReal := by
  rcases @prob_13_8_conditional_expectation_integrals Ω 𝓕 P 𝓖 h𝓖
      A B CP hCP hB hA with
    ⟨hnum, hden⟩
  have _hden_ne : ∫ ω, CP ω ∂P ≠ 0 := by
    rw [hden]
    exact hprobA
  rw [hnum, hden]

theorem prob_13_8_posterior_bridge {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {cell A : Set Ω}
    (hcell : @MeasurableSet Ω 𝓕 cell)
    (hA : @MeasurableSet Ω 𝓕 A)
    (hA0 : P A ≠ 0) :
    @def_13_1 Ω 𝓕 P A hA hA0 (measure_ne_top P A)
        (cell.indicator (fun _ => (1 : ℝ))) =
      (P (A ∩ cell)).toReal / (P A).toReal := by
  rw [@thm_13_1_indicator_formula Ω 𝓕 P A cell hA hA0 (measure_ne_top P A)]
  rw [@prob_13_8_indicator_integral_inter Ω 𝓕 P cell A hcell]

theorem prob_13_8_partition_atom_numerator {Ω ι : Type*}
    [𝓕 : MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕} {Cell : ι → Set Ω}
    {A : Set Ω} {CP : Ω → ℝ} (i : ι)
    (_hpart : def_13_2_isFinitePartition Cell)
    (hgen : @def_13_2_generatesSigmaField Ω ι 𝓖 Cell)
    (hCP : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 (A.indicator (fun _ => (1 : ℝ))) CP)
    (hA : @MeasurableSet Ω 𝓕 A)
    (hCell0 : P (Cell i) ≠ 0) :
    ∫ ω in Cell i, CP ω ∂P =
      @def_13_1 Ω 𝓕 P (Cell i) (h𝓖 (hgen.1 i))
          hCell0 (measure_ne_top P (Cell i))
          (A.indicator (fun _ => (1 : ℝ))) *
        (P (Cell i)).toReal := by
  rcases @prob_13_8_conditional_expectation_integrals Ω 𝓕 P 𝓖 h𝓖
      A (Cell i) CP hCP (hgen.1 i) hA with
    ⟨hnum, _hden⟩
  have hcond :
      @def_13_1 Ω 𝓕 P (Cell i) (h𝓖 (hgen.1 i))
          hCell0 (measure_ne_top P (Cell i))
          (A.indicator (fun _ => (1 : ℝ))) =
        (P (Cell i ∩ A)).toReal / (P (Cell i)).toReal := by
    rw [@thm_13_1_indicator_formula Ω 𝓕 P (Cell i) A
      (h𝓖 (hgen.1 i)) hCell0 (measure_ne_top P (Cell i))]
    rw [@prob_13_8_indicator_integral_inter Ω 𝓕 P A (Cell i) hA]
  rw [hnum, hcond]
  have hcellReal : (P (Cell i)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hCell0, measure_ne_top P (Cell i)⟩
  field_simp [hcellReal]

theorem prob_13_8_partition_classical_bayes {Ω ι : Type*}
    [𝓕 : MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
    {h𝓖 : IsSubSigmaField 𝓖 𝓕} {Cell : ι → Set Ω}
    {A : Set Ω} {CP : Ω → ℝ} (i : ι)
    (_hpart : def_13_2_isFinitePartition Cell)
    (hgen : @def_13_2_generatesSigmaField Ω ι 𝓖 Cell)
    (hCP : @def_13_3 Ω 𝓕 P 𝓖 h𝓖 (A.indicator (fun _ => (1 : ℝ))) CP)
    (hA : @MeasurableSet Ω 𝓕 A)
    (hA0 : P A ≠ 0)
    (hCell0 : P (Cell i) ≠ 0) :
    @def_13_1 Ω 𝓕 P A hA hA0 (measure_ne_top P A)
        ((Cell i).indicator (fun _ => (1 : ℝ))) =
      @def_13_1 Ω 𝓕 P (Cell i) (h𝓖 (hgen.1 i))
          hCell0 (measure_ne_top P (Cell i))
          (A.indicator (fun _ => (1 : ℝ))) *
        (P (Cell i)).toReal / (P A).toReal := by
  have hprobA : (P A).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hA0, measure_ne_top P A⟩
  have _hatom := @prob_13_8_partition_atom_numerator Ω ι 𝓕 _ P _ 𝓖 h𝓖
    Cell A CP i _hpart hgen hCP hA hCell0
  have hposterior := @prob_13_8_posterior_bridge Ω 𝓕 P _ (Cell i) A
    (h𝓖 (hgen.1 i)) hA hA0
  have hcond :
      @def_13_1 Ω 𝓕 P (Cell i) (h𝓖 (hgen.1 i))
          hCell0 (measure_ne_top P (Cell i))
          (A.indicator (fun _ => (1 : ℝ))) =
        (P (Cell i ∩ A)).toReal / (P (Cell i)).toReal := by
    rw [@thm_13_1_indicator_formula Ω 𝓕 P (Cell i) A
      (h𝓖 (hgen.1 i)) hCell0 (measure_ne_top P (Cell i))]
    rw [@prob_13_8_indicator_integral_inter Ω 𝓕 P A (Cell i) hA]
  rw [hposterior, hcond]
  rw [Set.inter_comm]
  have hcellReal : (P (Cell i)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hCell0, measure_ne_top P (Cell i)⟩
  field_simp [hcellReal, hprobA]

theorem prob_13_8 :
    (∀ {Ω : Type*} [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
      {𝓖 : SigmaField Ω} {h𝓖 : IsSubSigmaField 𝓖 𝓕}
      {A B : Set Ω} {CP : Ω → ℝ},
      @def_13_3 Ω 𝓕 P 𝓖 h𝓖 (A.indicator (fun _ => (1 : ℝ))) CP →
      IsMeasurableIn 𝓖 B →
      @MeasurableSet Ω 𝓕 A →
      (P A).toReal ≠ 0 →
      (∫ ω in B, CP ω ∂P) / (∫ ω, CP ω ∂P) =
        (P (B ∩ A)).toReal / (P A).toReal) ∧
    (∀ {Ω ι : Type*} [𝓕 : MeasurableSpace Ω] [Fintype ι]
      {P : Measure Ω} [IsFiniteMeasure P] {𝓖 : SigmaField Ω}
      {h𝓖 : IsSubSigmaField 𝓖 𝓕} {Cell : ι → Set Ω}
      {A : Set Ω} {CP : Ω → ℝ} (i : ι),
      ∀ (_hpart : def_13_2_isFinitePartition Cell)
        (hgen : @def_13_2_generatesSigmaField Ω ι 𝓖 Cell)
        (_hCP : @def_13_3 Ω 𝓕 P 𝓖 h𝓖
          (A.indicator (fun _ => (1 : ℝ))) CP)
        (hA : @MeasurableSet Ω 𝓕 A)
        (hA0 : P A ≠ 0)
        (hCell0 : P (Cell i) ≠ 0),
        @def_13_1 Ω 𝓕 P A hA hA0
            (measure_ne_top P A) ((Cell i).indicator (fun _ => (1 : ℝ))) =
          @def_13_1 Ω 𝓕 P (Cell i)
              (h𝓖 (hgen.1 i)) hCell0 (measure_ne_top P (Cell i))
              (A.indicator (fun _ => (1 : ℝ))) *
            (P (Cell i)).toReal / (P A).toReal) := by
  constructor
  · intro Ω 𝓕 P 𝓖 h𝓖 A B CP hCP hB hA hprobA
    exact @prob_13_8_generalized_bayes Ω 𝓕 P 𝓖 h𝓖 A B CP
      hCP hB hA hprobA
  · intro Ω ι 𝓕 _ P _ 𝓖 h𝓖 Cell A CP i hpart hgen hCP hA hA0 hCell0
    exact @prob_13_8_partition_classical_bayes Ω ι 𝓕 _ P _ 𝓖 h𝓖
      Cell A CP i hpart hgen hCP hA hA0 hCell0
