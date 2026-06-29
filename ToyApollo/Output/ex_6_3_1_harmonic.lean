import Mathlib

noncomputable section

namespace Ex631Harmonic

noncomputable def scaledTerm (c : ℝ) (n : ℕ) : NNReal :=
  Real.toNNReal (c * (1 / (n + 1 : ℝ)))

lemma scaledTerm_coe {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ((scaledTerm c n : NNReal) : ℝ) = c * (1 / (n + 1 : ℝ)) := by
  have hnonneg : 0 ≤ c * (1 / (n + 1 : ℝ)) := by
    have hn : 0 < (n + 1 : ℝ) := by positivity
    positivity
  rw [scaledTerm]
  exact congrArg (fun x : NNReal => (x : ℝ)) (Real.toNNReal_of_nonneg hnonneg)

set_option maxHeartbeats 800000 in
lemma scaledTerm_not_summable {c : ℝ} (hc : 0 < c) :
    ¬ Summable (fun n : ℕ => (scaledTerm c n : ℝ)) := by
  intro hs
  have hscaled : Summable (fun n : ℕ => c⁻¹ * ((scaledTerm c n : ℝ))) := hs.mul_left c⁻¹
  have hcongr : Summable (fun n : ℕ => (1 / (n + 1 : ℝ))) := by
    refine hscaled.congr ?_
    intro n
    rw [scaledTerm_coe hc n]
    field_simp [hc.ne']
  have hNot : ¬ Summable (fun n : ℕ => (1 / (n + 1 : ℝ))) := by
    intro h
    exact not_tendsto_atTop_of_tendsto_nhds h.hasSum.tendsto_sum_nat
      Real.tendsto_sum_range_one_div_nat_succ_atTop
  exact hNot hcongr

set_option maxHeartbeats 800000 in
lemma scaledTerm_tsum_eq_top {c : ℝ} (hc : 0 < c) :
    (∑' n : ℕ, ((scaledTerm c n : NNReal) : ENNReal)) = ⊤ := by
  exact (ENNReal.tsum_coe_eq_top_iff_not_summable_coe (f := scaledTerm c)).2
    (scaledTerm_not_summable hc)

end Ex631Harmonic
