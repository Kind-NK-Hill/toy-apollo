/-
TASK ID: ex_8_4_3
TYPE: Example_Proof
SOURCE PLAN: 34_chap8_total_variation_distance
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.ch8_discrete_pmf_core
import ToyApollo.Output.thm_8_6

open MeasureTheory Set
open Ch8DiscretePMFCore
open scoped BigOperators

noncomputable section

lemma poisson_tail_sum (lam : NNReal) :
    ∑' n, ProbabilityTheory.poissonPMFReal lam (n + 2)
      = 1 - Real.exp (-(lam : ℝ)) - (lam : ℝ) * Real.exp (-(lam : ℝ)) := by
  have htail :
      HasSum (fun n => ProbabilityTheory.poissonPMFReal lam (n + 2))
        (1 - Finset.sum (Finset.range 2) (fun i => ProbabilityTheory.poissonPMFReal lam i)) := by
    exact (hasSum_nat_add_iff' 2).2 (ProbabilityTheory.poissonPMFRealSum lam)
  rw [htail.tsum_eq]
  have hsum_two :
      Finset.sum (Finset.range 2) (fun i => ProbabilityTheory.poissonPMFReal lam i)
        = ProbabilityTheory.poissonPMFReal lam 0 + ProbabilityTheory.poissonPMFReal lam 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [hsum_two]
  simp [ProbabilityTheory.poissonPMFReal]
  ring

theorem ex_8_4_3 (lam : NNReal) (hlam : lam ≤ 1) :
    totalVariationDistance (bernoulliNatPMF lam hlam).toMeasure (ProbabilityTheory.poissonPMF lam).toMeasure
      = (lam : ℝ) * (1 - Real.exp (-(lam : ℝ))) := by
  let term : ℕ → ℝ := fun n =>
    |((bernoulliNatPMF lam hlam) n).toReal - ProbabilityTheory.poissonPMFReal lam n|
  have hsum_term : Summable term := by
    simpa [term, TVCore.pmfDiff, TVCore.pmfReal, poissonPMF_toReal] using
      (TVCore.summable_abs_pmfDiff (bernoulliNatPMF lam hlam) (ProbabilityTheory.poissonPMF lam))
  have hsplit : ∑' n, term n = (Finset.sum (Finset.range 2) term) + ∑' n, term (n + 2) := by
    simpa using (Summable.sum_add_tsum_nat_add 2 hsum_term).symm
  have hterm0 :
      term 0 = Real.exp (-(lam : ℝ)) + (lam : ℝ) - 1 := by
    have hineq : 1 - (lam : ℝ) ≤ Real.exp (-(lam : ℝ)) := Real.one_sub_le_exp_neg (lam : ℝ)
    have hnonpos : (1 - (lam : ℝ)) - Real.exp (-(lam : ℝ)) ≤ 0 := by
      linarith
    rw [show term 0 =
      |(1 - (lam : ℝ)) - ProbabilityTheory.poissonPMFReal lam 0| by
        simp [term, bernoulliNatPMF_zero, poissonPMF_toReal]]
    simp [ProbabilityTheory.poissonPMFReal, abs_of_nonpos hnonpos]
    ring
  have hlam_nonneg : 0 ≤ (lam : ℝ) := by exact_mod_cast lam.2
  have hExpLeOne : Real.exp (-(lam : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hterm1 :
      term 1 = (lam : ℝ) - (lam : ℝ) * Real.exp (-(lam : ℝ)) := by
    have hnonneg : 0 ≤ (lam : ℝ) - Real.exp (-(lam : ℝ)) * (lam : ℝ) := by
      nlinarith
    have hpoisson1 :
        ProbabilityTheory.poissonPMFReal lam 1 = Real.exp (-(lam : ℝ)) * (lam : ℝ) := by
      simp [ProbabilityTheory.poissonPMFReal, mul_comm, mul_left_comm, mul_assoc]
    rw [show term 1 = |(lam : ℝ) - ProbabilityTheory.poissonPMFReal lam 1| by
      simp [term, bernoulliNatPMF_one]]
    rw [hpoisson1]
    rw [abs_of_nonneg hnonneg]
    ring
  have htail_term :
      ∀ n, term (n + 2) = ProbabilityTheory.poissonPMFReal lam (n + 2) := by
    intro n
    have hbern : ((bernoulliNatPMF lam hlam) (n + 2)).toReal = 0 :=
      bernoulliNatPMF_ge_two lam hlam (by omega)
    have hnonneg : 0 ≤ ProbabilityTheory.poissonPMFReal lam (n + 2) :=
      ProbabilityTheory.poissonPMFReal_nonneg
    change
      |((bernoulliNatPMF lam hlam) (n + 2)).toReal - ProbabilityTheory.poissonPMFReal lam (n + 2)|
        = ProbabilityTheory.poissonPMFReal lam (n + 2)
    rw [hbern]
    simpa [sub_eq_add_neg, zero_add, abs_neg] using
      (abs_of_nonneg hnonneg : |ProbabilityTheory.poissonPMFReal lam (n + 2)| =
        ProbabilityTheory.poissonPMFReal lam (n + 2))
  have hsum_two : Finset.sum (Finset.range 2) term = term 0 + term 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
  calc
    totalVariationDistance (bernoulliNatPMF lam hlam).toMeasure (ProbabilityTheory.poissonPMF lam).toMeasure
        = (1 / 2 : ℝ) * ∑' n, term n := by
            simpa [term, poissonPMF_toReal] using
              (thm_8_6_discrete_pmf (bernoulliNatPMF lam hlam) (ProbabilityTheory.poissonPMF lam))
    _ = (1 / 2 : ℝ) * (Finset.sum (Finset.range 2) term + (∑' n, term (n + 2))) := by
            rw [hsplit]
    _ = (1 / 2 : ℝ) *
          (term 0 + term 1 + (∑' n, ProbabilityTheory.poissonPMFReal lam (n + 2))) := by
            congr 1
            rw [hsum_two]
            rw [tsum_congr htail_term]
    _ = (1 / 2 : ℝ) *
          ((Real.exp (-(lam : ℝ)) + (lam : ℝ) - 1)
            + ((lam : ℝ) - (lam : ℝ) * Real.exp (-(lam : ℝ)))
            + (1 - Real.exp (-(lam : ℝ)) - (lam : ℝ) * Real.exp (-(lam : ℝ)))) := by
            rw [hterm0, hterm1, poisson_tail_sum]
    _ = (lam : ℝ) * (1 - Real.exp (-(lam : ℝ))) := by
            ring
