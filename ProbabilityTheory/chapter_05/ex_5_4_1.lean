/-
TASK ID: ex_5_4_1
TYPE: Example_Proof
SOURCE PLAN: 16_chap5_borel_cantelli
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW
open Filter MeasureTheory Set
open scoped ENNReal Topology

 
noncomputable def fairCoin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

@[simp] theorem fairCoin_apply_singleton (b : Bool) : fairCoin {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> simp [fairCoin]

instance : IsProbabilityMeasure fairCoin := by
  refine ⟨by simpa [fairCoin] using ENNReal.inv_two_add_inv_two⟩

 
noncomputable def fairCoinSequenceMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => fairCoin

instance : IsProbabilityMeasure fairCoinSequenceMeasure := by
  dsimp [fairCoinSequenceMeasure]
  infer_instance



def headRunEvent (n : ℕ) : Set (ℕ → Bool) :=
  Set.pi (Finset.Icc n (2 * n)) (fun _ => ({true} : Set Bool))

lemma measurableSet_headRunEvent (n : ℕ) : MeasurableSet (headRunEvent n) := by
  refine MeasurableSet.pi (Finset.countable_toSet _) ?_
  intro i hi
  exact measurableSet_singleton true

lemma fairCoinSequenceMeasure_headRunEvent (n : ℕ) :
    fairCoinSequenceMeasure (headRunEvent n) = (1 / 2 : ℝ≥0∞) ^ (n + 1) := by
  rw [headRunEvent, fairCoinSequenceMeasure]
  rw [Measure.infinitePi_pi
      (μ := fun _ : ℕ => fairCoin)
      (s := Finset.Icc n (2 * n))
      (t := fun _ => ({true} : Set Bool))
      (mt := by
        intro i hi
        exact measurableSet_singleton true)]
  have h_exp : n + n + 1 - n = n + 1 := by
    omega
  simpa [fairCoin_apply_singleton, Finset.prod_const, two_mul, add_assoc] using
    congrArg (fun k : ℕ => (1 / 2 : ℝ≥0∞) ^ k) h_exp

lemma tsum_headRunEvent_ne_top :
    (∑' n, fairCoinSequenceMeasure (headRunEvent n)) ≠ ∞ := by
  rw [show (∑' n, fairCoinSequenceMeasure (headRunEvent n)) =
      ∑' n, (1 / 2 : ℝ≥0∞) ^ (n + 1) by
    congr with n
    exact fairCoinSequenceMeasure_headRunEvent n]
  simpa [one_div] using
    (show (∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1)) ≠ ∞ by
      rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
      simp)



lemma headRunEvent_one_inter_two :
    headRunEvent 1 ∩ headRunEvent 2 = Set.pi (Finset.Icc 1 4) (fun _ => ({true} : Set Bool)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨h1, h2⟩
    simp [headRunEvent] at h1 h2 ⊢
    intro i hi1 hi4
    by_cases hi2 : i ≤ 2
    · exact h1 i hi1 hi2
    · have h2i : 2 ≤ i := by omega
      exact h2 i h2i hi4
  · intro hx
    constructor <;> simp [headRunEvent] at hx ⊢
    · intro i hi1 hi2
      exact hx i hi1 (by omega)
    · intro i hi2 hi4
      exact hx i (by omega) hi4

lemma fairCoinSequenceMeasure_headRunEvent_one_inter_two :
    fairCoinSequenceMeasure (headRunEvent 1 ∩ headRunEvent 2) = (1 / 2 : ℝ≥0∞) ^ 4 := by
  rw [headRunEvent_one_inter_two, fairCoinSequenceMeasure]
  rw [Measure.infinitePi_pi
      (μ := fun _ : ℕ => fairCoin)
      (s := Finset.Icc 1 4)
      (t := fun _ => ({true} : Set Bool))
      (mt := by
        intro i hi
        exact measurableSet_singleton true)]
  simp [fairCoin_apply_singleton, Finset.prod_const]

lemma not_iIndepSet_headRunEvent :
    ¬ ProbabilityTheory.iIndepSet headRunEvent fairCoinSequenceMeasure := by
  intro h_indep
  have h_biInter :=
    (ProbabilityTheory.iIndepSet_iff_meas_biInter
      (μ := fairCoinSequenceMeasure) (f := headRunEvent) measurableSet_headRunEvent).mp h_indep
      ({1, 2} : Finset ℕ)
  have h_pair :
      fairCoinSequenceMeasure (headRunEvent 1 ∩ headRunEvent 2) =
        fairCoinSequenceMeasure (headRunEvent 1) * fairCoinSequenceMeasure (headRunEvent 2) := by
    simpa [Finset.prod_insert, Set.biInter_insert, inter_assoc, inter_left_comm, inter_comm] using
      h_biInter
  rw [fairCoinSequenceMeasure_headRunEvent_one_inter_two,
    fairCoinSequenceMeasure_headRunEvent, fairCoinSequenceMeasure_headRunEvent] at h_pair
  have h_pair_real := congrArg ENNReal.toReal h_pair
  norm_num at h_pair_real



theorem ex_5_4_1 :
    (∑' n, fairCoinSequenceMeasure (headRunEvent n)) ≠ ∞ ∧
      fairCoinSequenceMeasure (limsup headRunEvent atTop) = 0 ∧
      ¬ ProbabilityTheory.iIndepSet headRunEvent fairCoinSequenceMeasure := by
  refine ⟨tsum_headRunEvent_ne_top, ?_, not_iIndepSet_headRunEvent⟩
  simpa using
    MeasureTheory.measure_limsup_atTop_eq_zero
      (μ := fairCoinSequenceMeasure) (s := headRunEvent) tsum_headRunEvent_ne_top
