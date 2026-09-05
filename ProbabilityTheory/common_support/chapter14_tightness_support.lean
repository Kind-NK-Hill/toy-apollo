/-
TASK ID: chapter14_tightness_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_14.def_14_3




open MeasureTheory Set
open scoped Topology

noncomputable section

 
def chapter14_tailMass
    (P : ProbabilityMeasure ℝ) (M : ℝ) : ℝ :=
  (P : Measure ℝ).real {x : ℝ | M < |x|}

 
theorem chapter14_tailMass_mono
    (P : ProbabilityMeasure ℝ) {M0 M : ℝ} (hM : M0 ≤ M) :
    chapter14_tailMass P M ≤ chapter14_tailMass P M0 := by
  unfold chapter14_tailMass
  refine measureReal_mono ?_
  intro x hx
  exact lt_of_le_of_lt hM hx

 
def chapter14_uniformTailBound
    (Pseq : ℕ → ProbabilityMeasure ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 ≤ M ∧
    ∀ n : ℕ, chapter14_tailMass (Pseq n) M < ε

 
theorem chapter14_of_uniformTailBound
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (htail : chapter14_uniformTailBound Pseq) :
    def_14_3 Pseq := by
  intro ε hε
  rcases htail ε hε with ⟨M, hM_nonneg, htailM⟩
  refine ⟨M, hM_nonneg, ?_⟩
  intro n
  haveI : IsProbabilityMeasure (Pseq n : Measure ℝ) := (Pseq n).property
  let s : Set ℝ := Icc (-M) M
  have hs : MeasurableSet s := measurableSet_Icc
  have hcompl : sᶜ = {x : ℝ | M < |x|} := by
    ext x
    simp only [s, mem_compl_iff, mem_Icc, mem_setOf_eq]
    constructor
    · intro hnot
      by_cases hxlt : x < -M
      · have hneg : |x| = -x := by
          exact abs_of_neg (lt_of_lt_of_le hxlt (neg_nonpos.mpr hM_nonneg))
        rw [hneg]
        linarith
      · have hxge : -M ≤ x := le_of_not_gt hxlt
        have hxnotle : ¬ x ≤ M := fun hxle => hnot ⟨hxge, hxle⟩
        have hxM : M < x := lt_of_not_ge hxnotle
        exact lt_of_lt_of_le hxM (le_abs_self x)
    · intro hx hinside
      exact (not_lt.mpr (abs_le.mpr hinside)) hx
  have hsum := probReal_add_probReal_compl (μ := (Pseq n : Measure ℝ)) hs
  have htailn : (Pseq n : Measure ℝ).real sᶜ < ε := by
    simpa [chapter14_tailMass, hcompl] using htailM n
  change 1 - ε < (Pseq n : Measure ℝ).real s
  linarith

 
theorem chapter14_uniformTailBound_of_def_14_3
    (Pseq : ℕ → ProbabilityMeasure ℝ)
    (hTight : def_14_3 Pseq) :
    chapter14_uniformTailBound Pseq := by
  intro ε hε
  rcases hTight ε hε with ⟨M, hM_nonneg, hM⟩
  refine ⟨M, hM_nonneg, ?_⟩
  intro n
  haveI : IsProbabilityMeasure (Pseq n : Measure ℝ) := (Pseq n).property
  let s : Set ℝ := Icc (-M) M
  have hs : MeasurableSet s := measurableSet_Icc
  have hcompl : sᶜ = {x : ℝ | M < |x|} := by
    ext x
    simp only [s, mem_compl_iff, mem_Icc, mem_setOf_eq]
    constructor
    · intro hnot
      by_cases hxlt : x < -M
      · have hneg : |x| = -x := by
          exact abs_of_neg (lt_of_lt_of_le hxlt (neg_nonpos.mpr hM_nonneg))
        rw [hneg]
        linarith
      · have hxge : -M ≤ x := le_of_not_gt hxlt
        have hxnotle : ¬ x ≤ M := fun hxle => hnot ⟨hxge, hxle⟩
        have hxM : M < x := lt_of_not_ge hxnotle
        exact lt_of_lt_of_le hxM (le_abs_self x)
    · intro hx hinside
      exact (not_lt.mpr (abs_le.mpr hinside)) hx
  have hsum := probReal_add_probReal_compl (μ := (Pseq n : Measure ℝ)) hs
  have hinside : 1 - ε < (Pseq n : Measure ℝ).real s := by
    simpa [s] using hM n
  have htail : (Pseq n : Measure ℝ).real sᶜ < ε := by
    linarith
  simpa [chapter14_tailMass, hcompl] using htail
