/-
TASK ID: ex_3_1_2
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_3_1
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set ENNReal Function MeasureTheory

inductive GeneratedField {Ω : Type*} (S : Set (Set Ω)) : Set (Set Ω)
  | basic (s : Set Ω) (h : s ∈ S) : GeneratedField S s
  | empty : GeneratedField S ∅
  | compl (s : Set Ω) (h : GeneratedField S s) : GeneratedField S sᶜ
  | union (s t : Set Ω) (hs : GeneratedField S s) (ht : GeneratedField S t) : GeneratedField S (s ∪ t)

def B0_generators : Set (Set ℝ) :=
  { s | (∃ a b : ℝ, s = Ioc a b) ∨ (∃ b : ℝ, s = Iic b) ∨ (∃ a : ℝ, s = Ioi a) ∨ s = univ }

def B0 : FieldOfSets ℝ where
  carrier := GeneratedField B0_generators
  empty_mem := GeneratedField.empty
  compl_mem := GeneratedField.compl
  union_mem := GeneratedField.union

theorem measurable_of_mem_B0 (s : Set ℝ) (h : s ∈ B0.carrier) : MeasurableSet s := by
  induction h with
  | basic s hs =>
    rcases hs with (⟨a, b, rfl⟩ | ⟨b, rfl⟩ | ⟨a, rfl⟩ | rfl)
    · exact measurableSet_Ioc
    · exact measurableSet_Iic
    · exact measurableSet_Ioi
    · exact MeasurableSet.univ
  | empty => exact MeasurableSet.empty
  | compl s _ ih => exact ih.compl
  | union s t _ _ ihs iht => exact ihs.union iht

noncomputable def Example_3_1_2 : Premeasure B0 :=
  { μ₀ := fun s => volume s.val,
    map_empty := measure_empty,
    sigma_additive := fun A hA hU h_disj => by
      -- All sets in the sequence are in the field, thus Borel measurable.
      have h_meas : ∀ i, MeasurableSet (A i) := fun i => measurable_of_mem_B0 (A i) (hA i)
      -- Countable additivity for the Lebesgue measure (volume) proves the result.
      exact measure_iUnion h_disj h_meas }
