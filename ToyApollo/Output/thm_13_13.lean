/-
TASK ID: thm_13_13
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-discrete-random-variable
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_13_12

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped BigOperators

noncomputable section

def thm_13_13_atom {Ω : Type*} (Y : Ω → ℕ) (y : ℕ) : Set Ω :=
  {ω | Y ω = y}

theorem thm_13_13_atoms_countablePartition {Ω : Type*} (Y : Ω → ℕ) :
    thm_13_12_countablePartition (thm_13_13_atom Y) := by
  constructor
  · intro ω
    exact ⟨Y ω, rfl⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro ω hi hj
    exact hij (hi.symm.trans hj)

def thm_13_13_discreteJointLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℕ) (pXY : ℕ → ℕ → ℝ) (pY : ℕ → ℝ) : Prop :=
  (∀ y : ℕ, pY y = ∑' x : ℕ, pXY x y) ∧
    (∀ x y : ℕ, pXY x y =
      (P {ω | X ω = x ∧ Y ω = y}).toReal) ∧
    (∀ y : ℕ, pY y = (P (thm_13_13_atom Y y)).toReal)

def thm_13_13_conditionalPMF
    (pXY : ℕ → ℕ → ℝ) (pY : ℕ → ℝ) (x y : ℕ) : ℝ :=
  pXY x y / pY y

def thm_13_13_conditionalExpectationFormula
    (g : ℕ → ℝ) (pXY : ℕ → ℕ → ℝ) (pY : ℕ → ℝ) (y : ℕ) : ℝ :=
  ∑' x : ℕ, g x * thm_13_13_conditionalPMF pXY pY x y

def thm_13_13_identityConditionalExpectationFormula
    (pXY : ℕ → ℕ → ℝ) (pY : ℕ → ℝ) (y : ℕ) : ℝ :=
  thm_13_13_conditionalExpectationFormula (fun x : ℕ => (x : ℝ)) pXY pY y

def thm_13_13_conditionalExpectationGivenValue {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X Y : Ω → ℕ) (g : ℕ → ℝ) (y : ℕ)
    (hY : Measurable Y) (hAtom0 : P (thm_13_13_atom Y y) ≠ 0) : ℝ :=
  def_13_1 P (thm_13_13_atom Y y)
    (hY (measurableSet_singleton y)) hAtom0
    (measure_ne_top P (thm_13_13_atom Y y)) (fun ω => g (X ω))

def thm_13_13_partitionConditionalExpectation {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (X Y : Ω → ℕ)
    (g : ℕ → ℝ) : Ω → ℝ :=
  thm_13_12_countablePartitionConditionalExpectation P
    (thm_13_13_atom Y) (fun ω => g (X ω))

theorem thm_13_13_partitionConditionalExpectation_apply {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (X Y : Ω → ℕ)
    (g : ℕ → ℝ) (hY : Measurable Y) {y : ℕ} {ω : Ω}
    (hAtom0 : P (thm_13_13_atom Y y) ≠ 0)
    (hω : ω ∈ thm_13_13_atom Y y) :
    thm_13_13_partitionConditionalExpectation P X Y g ω =
      thm_13_13_conditionalExpectationGivenValue P X Y g y hY hAtom0 := by
  rw [thm_13_13_partitionConditionalExpectation]
  exact thm_13_12_countablePartitionConditionalExpectation_of_mem_wellDefined
    P (fun ω => g (X ω)) (thm_13_13_atoms_countablePartition Y) hω
    (hY (measurableSet_singleton y)) hAtom0

def thm_13_13_atomIntegralSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℕ) (g : ℕ → ℝ)
    (pXY : ℕ → ℕ → ℝ) : Prop :=
  ∀ y : ℕ,
    (∫ ω in thm_13_13_atom Y y, g (X ω) ∂P) =
      ∑' x : ℕ, g x * pXY x y

theorem thm_13_13_atomIntegral_from_jointLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℕ) (g : ℕ → ℝ) (pXY : ℕ → ℕ → ℝ) (pY : ℕ → ℝ)
    (hX : Measurable X)
    (hInt : Integrable (fun ω => g (X ω)) P)
    (hLaw : thm_13_13_discreteJointLaw P X Y pXY pY) :
    thm_13_13_atomIntegralSupport P X Y g pXY := by
  intro y
  let μy : Measure ℕ := Measure.map X (P.restrict (thm_13_13_atom Y y))
  have hg_sm : AEStronglyMeasurable g μy := by
    exact (measurable_of_countable g).aestronglyMeasurable
  have hX_ae : AEMeasurable X (P.restrict (thm_13_13_atom Y y)) :=
    hX.aemeasurable
  have hg_int_map : Integrable g μy := by
    exact (integrable_map_measure hg_sm hX_ae).2 hInt.integrableOn
  calc
    (∫ ω in thm_13_13_atom Y y, g (X ω) ∂P)
        = ∫ x, g x ∂μy := by
          symm
          exact integral_map hX_ae hg_sm
    _ = ∑' x : ℕ, μy.real {x} • g x := by
          exact integral_countable hg_int_map
    _ = ∑' x : ℕ, g x * pXY x y := by
          apply tsum_congr
          intro x
          have hμ : μy.real {x} = pXY x y := by
            calc
              μy.real {x}
                  = ((P.restrict (thm_13_13_atom Y y)) (X ⁻¹' {x})).toReal := by
                      simp [μy, measureReal_def,
                        Measure.map_apply hX (measurableSet_singleton x)]
              _ = (P ((X ⁻¹' {x}) ∩ thm_13_13_atom Y y)).toReal := by
                      rw [Measure.restrict_apply (hX (measurableSet_singleton x))]
              _ = (P {ω : Ω | X ω = x ∧ Y ω = y}).toReal := by
                      congr 1
              _ = pXY x y := (hLaw.2.1 x y).symm
          rw [hμ]
          simp [mul_comm]

theorem thm_13_13_conditionalPMFSeries
    (g : ℕ → ℝ) (pXY : ℕ → ℕ → ℝ) (pY : ℕ → ℝ) (y : ℕ) :
    (∑' x : ℕ, g x * thm_13_13_conditionalPMF pXY pY x y) =
      (∑' x : ℕ, g x * pXY x y) / pY y := by
  rw [div_eq_mul_inv, ← tsum_mul_right]
  congr with x
  simp [thm_13_13_conditionalPMF, div_eq_mul_inv]
  ring

theorem thm_13_13 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℕ) (g : ℕ → ℝ) (pXY : ℕ → ℕ → ℝ) (pY : ℕ → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hInt : Integrable (fun ω => g (X ω)) P)
    (hLaw : thm_13_13_discreteJointLaw P X Y pXY pY)
    (y : ℕ) (hAtom0 : P (thm_13_13_atom Y y) ≠ 0) :
    thm_13_13_conditionalExpectationGivenValue P X Y g y hY hAtom0 =
      thm_13_13_conditionalExpectationFormula g pXY pY y := by
  let hIntegral := thm_13_13_atomIntegral_from_jointLaw P X Y g pXY pY hX hInt hLaw
  calc
    thm_13_13_conditionalExpectationGivenValue P X Y g y hY hAtom0
        = (∫ ω in thm_13_13_atom Y y, g (X ω) ∂P) /
            (P (thm_13_13_atom Y y)).toReal := by
          exact thm_13_12_def_13_1_simple_formula P (thm_13_13_atom Y y)
            (hY (measurableSet_singleton y)) hAtom0
            (measure_ne_top P (thm_13_13_atom Y y)) (fun ω => g (X ω))
    _ = (∑' x : ℕ, g x * pXY x y) / pY y := by
          rw [hIntegral y, ← hLaw.2.2 y]
    _ = thm_13_13_conditionalExpectationFormula g pXY pY y := by
          rw [thm_13_13_conditionalExpectationFormula,
            thm_13_13_conditionalPMFSeries]

theorem thm_13_13_partitionFormula_on_atom {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℕ) (g : ℕ → ℝ) (pXY : ℕ → ℕ → ℝ) (pY : ℕ → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hInt : Integrable (fun ω => g (X ω)) P)
    (hLaw : thm_13_13_discreteJointLaw P X Y pXY pY)
    {y : ℕ} {ω : Ω} (hAtom0 : P (thm_13_13_atom Y y) ≠ 0)
    (hω : ω ∈ thm_13_13_atom Y y) :
    thm_13_13_partitionConditionalExpectation P X Y g ω =
      thm_13_13_conditionalExpectationFormula g pXY pY y := by
  rw [thm_13_13_partitionConditionalExpectation_apply P X Y g hY hAtom0 hω]
  exact thm_13_13 P X Y g pXY pY hX hY hInt hLaw y hAtom0

theorem thm_13_13_version_on_atom {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℕ) (g : ℕ → ℝ) (pXY : ℕ → ℕ → ℝ) (pY : ℕ → ℝ)
    (CE : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hInt : Integrable (fun ω => g (X ω)) P)
    (hLaw : thm_13_13_discreteJointLaw P X Y pXY pY)
    {y : ℕ} (hAtom0 : P (thm_13_13_atom Y y) ≠ 0)
    (hAtomValue :
      ∀ ω ∈ thm_13_13_atom Y y,
        CE ω = thm_13_13_conditionalExpectationGivenValue P X Y g y hY hAtom0)
    {ω : Ω} (hω : ω ∈ thm_13_13_atom Y y) :
    CE ω = thm_13_13_conditionalExpectationFormula g pXY pY y := by
  rw [hAtomValue ω hω]
  exact thm_13_13 P X Y g pXY pY hX hY hInt hLaw y hAtom0

theorem thm_13_13_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℕ) (pXY : ℕ → ℕ → ℝ) (pY : ℕ → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hInt : Integrable (fun ω => (X ω : ℝ)) P)
    (hLaw : thm_13_13_discreteJointLaw P X Y pXY pY)
    (y : ℕ) (hAtom0 : P (thm_13_13_atom Y y) ≠ 0) :
    thm_13_13_conditionalExpectationGivenValue P X Y
        (fun x : ℕ => (x : ℝ)) y hY hAtom0 =
      thm_13_13_identityConditionalExpectationFormula pXY pY y := by
  exact thm_13_13 P X Y (fun x : ℕ => (x : ℝ)) pXY pY hX hY
    hInt hLaw y hAtom0
