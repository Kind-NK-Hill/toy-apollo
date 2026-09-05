/-
TASK ID: ch8_bernoulli_bool_core
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_08.def_8_5

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Ch8BernoulliBoolCore

 
noncomputable def bernoulliMeasure (p : NNReal) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

lemma bernoulliMeasure_real_true (p : NNReal) (hp : p ≤ 1) :
    (bernoulliMeasure p hp).real {true} = p := by
  rw [bernoulliMeasure, Measure.real_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton true), PMF.bernoulli_apply]
  simp

lemma bernoulliMeasure_real_false (p : NNReal) (hp : p ≤ 1) :
    (bernoulliMeasure p hp).real {false} = 1 - p := by
  rw [bernoulliMeasure, Measure.real_def,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton false), PMF.bernoulli_apply]
  simp
  rw [ENNReal.toReal_sub_of_le]
  · norm_num
  · exact_mod_cast hp
  · simp

lemma bernoulliMeasure_apply_univ (p : NNReal) (hp : p ≤ 1) :
    bernoulliMeasure p hp Set.univ = 1 := by
  have huniv :
      (Set.univ : Set Bool) = ((↑(Finset.univ : Finset Bool) : Finset Bool) : Set Bool) := by
    ext b
    simp
  rw [huniv, bernoulliMeasure, PMF.toMeasure_apply_finset]
  simpa [tsum_fintype] using (PMF.tsum_coe (PMF.bernoulli p hp))

lemma boolBernoulli_totalVariationDistance_eq_abs (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1) :
    totalVariationDistance (bernoulliMeasure p hp) (bernoulliMeasure q hq) = |(p : ℝ) - q| := by
  let P := bernoulliMeasure p hp
  let Q := bernoulliMeasure q hq
  let S : Set ℝ :=
    {d : ℝ | ∃ A : Set Bool, MeasurableSet A ∧ d = |P.real A - Q.real A|}
  have hupper : ∀ d ∈ S, d ≤ |(p : ℝ) - q| := by
    intro d hd
    rcases hd with ⟨A, hA, rfl⟩
    have hclass : A = ∅ ∨ A = {true} ∨ A = {false} ∨ A = Set.univ := by
      by_cases ht : true ∈ A <;> by_cases hf : false ∈ A
      · right; right; right
        ext b
        cases b <;> simp [hf, ht]
      · right; left
        ext b
        cases b <;> simp [hf, ht]
      · right; right; left
        ext b
        cases b <;> simp [hf, ht]
      · left
        ext b
        cases b <;> simp [hf, ht]
    rcases hclass with rfl | rfl | rfl | rfl
    · rw [Measure.real_def, Measure.real_def]
      norm_num
    · have hEq : |P.real {true} - Q.real {true}| = |(p : ℝ) - q| := by
        rw [bernoulliMeasure_real_true p hp, bernoulliMeasure_real_true q hq]
      exact le_of_eq hEq
    · rw [bernoulliMeasure_real_false p hp, bernoulliMeasure_real_false q hq]
      have hrewrite : (1 - (p : ℝ)) - (1 - (q : ℝ)) = (q : ℝ) - p := by ring
      rw [hrewrite]
      simpa [abs_sub_comm] using le_rfl
    · have hPu : P Set.univ = 1 := by
        simpa [P] using bernoulliMeasure_apply_univ p hp
      have hQu : Q Set.univ = 1 := by
        simpa [Q] using bernoulliMeasure_apply_univ q hq
      rw [Measure.real_def, Measure.real_def, hPu, hQu]
      norm_num
  have hbounded : BddAbove S := ⟨|(p : ℝ) - q|, hupper⟩
  have hmem : |(p : ℝ) - q| ∈ S := by
    refine ⟨{true}, measurableSet_singleton true, ?_⟩
    rw [bernoulliMeasure_real_true p hp, bernoulliMeasure_real_true q hq]
  have hnonempty : S.Nonempty := ⟨|(p : ℝ) - q|, hmem⟩
  unfold totalVariationDistance
  change sSup S = |(p : ℝ) - q|
  apply le_antisymm
  · exact csSup_le hnonempty hupper
  · exact le_csSup hbounded hmem

end Ch8BernoulliBoolCore

end
