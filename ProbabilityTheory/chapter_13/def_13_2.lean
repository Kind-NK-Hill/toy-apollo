/-
TASK ID: def_13_2
TYPE: Definition
SOURCE PLAN: chapter13-finite-partition
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_1




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped BigOperators

noncomputable section



def def_13_2_isFinitePartition {Ω ι : Type*} (A : ι → Set Ω) : Prop :=
  (∀ ω : Ω, ∃ i : ι, ω ∈ A i) ∧
    ∀ i j : ι, i ≠ j → Disjoint (A i) (A j)



def def_13_2_generatesSigmaField {Ω ι : Type*}
    (𝓖 : MeasurableSpace Ω) (A : ι → Set Ω) : Prop :=
  (∀ i : ι, @MeasurableSet Ω 𝓖 (A i)) ∧
    ∀ 𝓗 : MeasurableSpace Ω,
      (∀ i : ι, @MeasurableSet Ω 𝓗 (A i)) →
        ∀ ⦃B : Set Ω⦄, @MeasurableSet Ω 𝓖 B → @MeasurableSet Ω 𝓗 B



def def_13_2_sourceDomain {Ω ι : Type*} [𝓕 : MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (𝓖 : MeasurableSpace Ω) (A : ι → Set Ω) (X : Ω → ℝ) : Prop :=
  IsProbabilityMeasure P ∧
    def_13_2_isFinitePartition A ∧
      (∀ i : ι, MeasurableSet (A i)) ∧
        (∀ i : ι, P (A i) ≠ ⊤) ∧
          def_13_2_generatesSigmaField 𝓖 A ∧
            (∀ ⦃B : Set Ω⦄, @MeasurableSet Ω 𝓖 B → @MeasurableSet Ω 𝓕 B) ∧
              Measurable[𝓖] X ∧
                Integrable X P



def def_13_2_atomConditionalExpectation {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ι → Set Ω) (X : Ω → ℝ) (i : ι)
    (hA : MeasurableSet (A i)) (hA_top : P (A i) ≠ ⊤) : ℝ := by
  classical
  exact
    if hA0 : P (A i) = 0 then
      0
    else
      def_13_1 P (A i) hA hA0 hA_top X

 
def def_13_2_atomTerm {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ι → Set Ω) (X : Ω → ℝ)
    (hA : ∀ i : ι, MeasurableSet (A i))
    (hA_top : ∀ i : ι, P (A i) ≠ ⊤) (i : ι) : Ω → ℝ :=
  (A i).indicator
    (fun _ => def_13_2_atomConditionalExpectation P A X i (hA i) (hA_top i))



def def_13_2_finitePartitionConditionalExpectation {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (A : ι → Set Ω) (X : Ω → ℝ)
    (hA : ∀ i : ι, MeasurableSet (A i))
    (hA_top : ∀ i : ι, P (A i) ≠ ⊤) : Ω → ℝ := by
  classical
  exact fun ω => ∑ i, def_13_2_atomTerm P A X hA hA_top i ω

theorem def_13_2_atomTerm_of_mem {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ι → Set Ω) (X : Ω → ℝ)
    (hA : ∀ i : ι, MeasurableSet (A i))
    (hA_top : ∀ i : ι, P (A i) ≠ ⊤) (i : ι) {ω : Ω}
    (hω : ω ∈ A i) :
    def_13_2_atomTerm P A X hA hA_top i ω =
      def_13_2_atomConditionalExpectation P A X i (hA i) (hA_top i) := by
  simp [def_13_2_atomTerm, hω]

theorem def_13_2_atomConditionalExpectation_of_wellDefined {Ω ι : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) (A : ι → Set Ω) (X : Ω → ℝ) (i : ι)
    (hA : MeasurableSet (A i)) (hA0 : P (A i) ≠ 0)
    (hA_top : P (A i) ≠ ⊤) :
    def_13_2_atomConditionalExpectation P A X i hA hA_top =
      def_13_1 P (A i) hA hA0 hA_top X := by
  rw [def_13_2_atomConditionalExpectation]
  simp [hA0]

theorem def_13_2_atomConditionalExpectation_of_null {Ω ι : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) (A : ι → Set Ω) (X : Ω → ℝ) (i : ι)
    (hA : MeasurableSet (A i)) (hA_top : P (A i) ≠ ⊤)
    (hA0 : P (A i) = 0) :
    def_13_2_atomConditionalExpectation P A X i hA hA_top = 0 := by
  rw [def_13_2_atomConditionalExpectation]
  simp [hA0]

theorem def_13_2_atomTerm_of_mem_wellDefined {Ω ι : Type*}
    [MeasurableSpace Ω]
    (P : Measure Ω) (A : ι → Set Ω) (X : Ω → ℝ)
    (hA : ∀ i : ι, MeasurableSet (A i))
    (hA_top_all : ∀ i : ι, P (A i) ≠ ⊤) (i : ι) {ω : Ω}
    (hω : ω ∈ A i)
    (hA0 : P (A i) ≠ 0) (hA_top_i : P (A i) ≠ ⊤) :
    def_13_2_atomTerm P A X hA hA_top_all i ω =
      def_13_1 P (A i) (hA i) hA0 hA_top_i X := by
  rw [def_13_2_atomTerm_of_mem P A X hA hA_top_all i hω]
  exact def_13_2_atomConditionalExpectation_of_wellDefined
    P A X i (hA i) hA0 hA_top_i

theorem def_13_2_atomTerm_of_not_mem {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : ι → Set Ω) (X : Ω → ℝ)
    (hA : ∀ i : ι, MeasurableSet (A i))
    (hA_top : ∀ i : ι, P (A i) ≠ ⊤) (i : ι) {ω : Ω}
    (hω : ω ∉ A i) :
    def_13_2_atomTerm P A X hA hA_top i ω = 0 := by
  simp [def_13_2_atomTerm, hω]

theorem def_13_2_apply {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (A : ι → Set Ω) (X : Ω → ℝ)
    (hA : ∀ i : ι, MeasurableSet (A i))
    (hA_top : ∀ i : ι, P (A i) ≠ ⊤) (ω : Ω) :
    def_13_2_finitePartitionConditionalExpectation P A X hA hA_top ω =
      ∑ i, def_13_2_atomTerm P A X hA hA_top i ω := by
  classical
  rfl



def def_13_2 {Ω ι : Type*} [𝓕 : MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (𝓖 : MeasurableSpace Ω) (A : ι → Set Ω)
    (X Y : Ω → ℝ) : Prop :=
  @def_13_2_sourceDomain Ω ι 𝓕 _ P 𝓖 A X ∧
    ∃ hA : ∀ i : ι, @MeasurableSet Ω 𝓕 (A i),
      ∃ hA_top : ∀ i : ι, P (A i) ≠ ⊤,
        Y = @def_13_2_finitePartitionConditionalExpectation Ω ι 𝓕 _
          P A X hA hA_top

theorem def_13_2_formula {Ω ι : Type*} [𝓕 : MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {𝓖 : MeasurableSpace Ω} {A : ι → Set Ω}
    {X Y : Ω → ℝ} (h : @def_13_2 Ω ι 𝓕 _ P 𝓖 A X Y) :
    ∃ hA : ∀ i : ι, @MeasurableSet Ω 𝓕 (A i),
      ∃ hA_top : ∀ i : ι, P (A i) ≠ ⊤,
        Y = @def_13_2_finitePartitionConditionalExpectation Ω ι 𝓕 _
          P A X hA hA_top :=
  h.2
