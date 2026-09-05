/-
TASK ID: prob_5_4
TYPE: Problem
SOURCE PLAN: 18_chap5_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

noncomputable section counterexample

private def myP : Measure (Fin 2) := (2⁻¹ : ℝ≥0∞) • Measure.count
private def myA : ℕ → Set (Fin 2) := fun _ => {0}

private lemma myP_isProbabilityMeasure : IsProbabilityMeasure myP := by
  constructor
  simp [myP, Measure.count_apply_finite]
  simp [ENNReal.inv_mul_cancel]

private lemma myA_meas : ∀ n, MeasurableSet (myA n) := by
  intro n
  exact Set.Finite.measurableSet (Set.finite_singleton _)

private lemma myP_myA : ∀ n, myP (myA n) = 2⁻¹ := by
  intro n
  simp only [myA, myP, Measure.smul_apply, smul_eq_mul]
  rw [Measure.count_apply_finite _ (Set.finite_singleton _)]
  simp

private lemma sum_diverges : ∑' n, myP (myA n) = ∞ := by
  simp only [myP_myA]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (by simp)

private lemma not_indep : ¬ iIndepSet myA myP := by
  intro h_ind
  have h_inter :
      myP (⋂ i ∈ ({0, 1} : Finset ℕ), myA i) =
        ∏ i ∈ ({0, 1} : Finset ℕ), myP (myA i) := by
    exact iIndepSet.meas_biInter h_ind {0, 1}
  simp [myP, myA] at h_inter
  rw [← ENNReal.toReal_eq_toReal_iff'] at h_inter <;> norm_num at *

private lemma limsup_ne_one : myP (limsup myA atTop) ≠ 1 := by
  unfold myP myA
  norm_num

theorem prob_5_4 :
    ∃ (Ω : Type) (𝒜 : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (A : ℕ → Set Ω) (_ : ∀ n, MeasurableSet (A n))
      (_ : ∑' n, P (A n) = ∞) (_ : ¬ iIndepSet A P),
      P (limsup A atTop) ≠ 1 :=
  ⟨Fin 2, inferInstance, myP, myP_isProbabilityMeasure, myA, myA_meas,
   sum_diverges, not_indep, limsup_ne_one⟩

end counterexample
