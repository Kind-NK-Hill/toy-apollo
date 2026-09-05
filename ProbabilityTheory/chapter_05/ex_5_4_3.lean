/-
TASK ID: ex_5_4_3
TYPE: Example_Proof
SOURCE PLAN: 16_chap5_borel_cantelli
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

section RandomBits

variable {p : ℕ → ℝ≥0∞}

 
noncomputable def bernoulliMeasure (q : ℝ≥0∞) : Measure Bool :=
  q • Measure.dirac true + (1 - q) • Measure.dirac false

@[simp] lemma bernoulliMeasure_apply_true (q : ℝ≥0∞) :
    bernoulliMeasure q ({true} : Set Bool) = q := by
  by_cases hq : q = ∞
  · simp [_root_.bernoulliMeasure, hq]
  · simp [_root_.bernoulliMeasure, hq]

@[simp] lemma bernoulliMeasure_apply_false (q : ℝ≥0∞) (hq : q ≤ 1) :
    bernoulliMeasure q ({false} : Set Bool) = 1 - q := by
  by_cases hq' : q = ∞
  · simp [_root_.bernoulliMeasure, hq'] at hq
  · simp [_root_.bernoulliMeasure, hq', hq]

lemma bernoulliMeasure_isProbabilityMeasure (p : ℕ → ℝ≥0∞)
    (hp : ∀ n, p n ≤ 1) (n : ℕ) :
    IsProbabilityMeasure (bernoulliMeasure (p n)) := by
  refine ⟨?_⟩
  have hpn := hp n
  have hsum : p n + (1 - p n) = 1 := by
    simpa [add_comm] using tsub_add_cancel_of_le hpn
  simpa [_root_.bernoulliMeasure, hsum]

 
noncomputable def bitStreamMeasure (p : ℕ → ℝ≥0∞) : Measure (ℕ → Bool) :=
  Measure.infinitePi fun n : ℕ => bernoulliMeasure (p n)

lemma bitStreamMeasure_isProbabilityMeasure (p : ℕ → ℝ≥0∞)
    (hp : ∀ n, p n ≤ 1) : IsProbabilityMeasure (bitStreamMeasure p) := by
  letI : ∀ n, IsProbabilityMeasure (bernoulliMeasure (p n)) := fun n =>
    bernoulliMeasure_isProbabilityMeasure (p := p) hp n
  dsimp [bitStreamMeasure]
  infer_instance

 
def oneEvent (n : ℕ) : Set (ℕ → Bool) := {x | x n = true}

lemma measurableSet_oneEvent (n : ℕ) : MeasurableSet (oneEvent n) := by
  change MeasurableSet ((fun x : ℕ → Bool => x n) ⁻¹' ({true} : Set Bool))
  exact (measurable_pi_apply n) (measurableSet_singleton true)

lemma iIndepFun_bits (p : ℕ → ℝ≥0∞) (hp : ∀ n, p n ≤ 1) :
    iIndepFun (fun n (x : ℕ → Bool) => x n) (bitStreamMeasure p) := by
  letI : ∀ n, IsProbabilityMeasure (bernoulliMeasure (p n)) := fun n =>
    bernoulliMeasure_isProbabilityMeasure (p := p) hp n
  simpa [bitStreamMeasure] using
    (ProbabilityTheory.iIndepFun_infinitePi
      (P := fun n : ℕ => bernoulliMeasure (p n))
      (X := fun _ b => b)
      (fun _ => measurable_id))

lemma iIndepSet_oneEvent (p : ℕ → ℝ≥0∞) (hp : ∀ n, p n ≤ 1) :
    iIndepSet oneEvent (bitStreamMeasure p) := by
  refine (iIndepSet_iff_meas_biInter
    (f := oneEvent)
    (μ := bitStreamMeasure p)
    (hf := measurableSet_oneEvent)).2 ?_
  intro s
  change
    bitStreamMeasure p
        (⋂ i ∈ s, (fun x : ℕ → Bool => x i) ⁻¹' ({true} : Set Bool)) =
      ∏ i ∈ s, bitStreamMeasure p
        ((fun x : ℕ → Bool => x i) ⁻¹' ({true} : Set Bool))
  exact (iIndepFun_bits p hp).measure_inter_preimage_eq_mul s
    (fun _ _ => measurableSet_singleton true)

@[simp] lemma bitStreamMeasure_oneEvent (p : ℕ → ℝ≥0∞) (hp : ∀ n, p n ≤ 1) (n : ℕ) :
    bitStreamMeasure p (oneEvent n) = p n := by
  letI : ∀ n, IsProbabilityMeasure (bernoulliMeasure (p n)) := fun n =>
    bernoulliMeasure_isProbabilityMeasure (p := p) hp n
  rw [show oneEvent n = (fun x : ℕ → Bool => x n) ⁻¹' ({true} : Set Bool) by
      ext x
      simp [oneEvent]]
  rw [← Measure.map_apply (measurable_pi_apply n) (measurableSet_singleton true)]
  rw [bitStreamMeasure, Measure.infinitePi_map_eval]
  exact bernoulliMeasure_apply_true (p n)

lemma finitely_many_ones_ae_of_tsum_ne_top (p : ℕ → ℝ≥0∞)
    (hp : ∀ n, p n ≤ 1)
    (hfinite : (∑' n, p n) ≠ ∞) :
    bitStreamMeasure p (limsup oneEvent atTop) = 0 := by
  letI : IsProbabilityMeasure (bitStreamMeasure p) :=
    bitStreamMeasure_isProbabilityMeasure (p := p) hp
  have hsum :
      (∑' n, bitStreamMeasure p (oneEvent n)) ≠ ∞ := by
    rw [show (∑' n, bitStreamMeasure p (oneEvent n)) = ∑' n, p n by
      congr with n
      exact bitStreamMeasure_oneEvent p hp n]
    exact hfinite
  simpa using
    MeasureTheory.measure_limsup_atTop_eq_zero
      (μ := bitStreamMeasure p)
      (s := oneEvent)
      hsum

lemma infinitely_many_ones_ae_of_tsum_eq_top (p : ℕ → ℝ≥0∞)
    (hp : ∀ n, p n ≤ 1)
    (hdiv : (∑' n, p n) = ∞) :
    bitStreamMeasure p (limsup oneEvent atTop) = 1 := by
  letI : IsProbabilityMeasure (bitStreamMeasure p) :=
    bitStreamMeasure_isProbabilityMeasure (p := p) hp
  have hsum :
      (∑' n, bitStreamMeasure p (oneEvent n)) = ∞ := by
    rw [show (∑' n, bitStreamMeasure p (oneEvent n)) = ∑' n, p n by
      congr with n
      exact bitStreamMeasure_oneEvent p hp n]
    exact hdiv
  exact ProbabilityTheory.measure_limsup_eq_one
    (hsm := measurableSet_oneEvent)
    (hs := iIndepSet_oneEvent p hp)
    (hs' := hsum)

 
noncomputable def bitProb (s : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / ((n + 1 : ℝ) ^ s))

lemma bitProb_le_one {s : ℝ} (hs : 0 < s) (n : ℕ) :
    bitProb s n ≤ 1 := by
  rw [bitProb]
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpow_ge_one : (1 : ℝ) ≤ (n + 1 : ℝ) ^ s := by
    have hbase : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact Real.one_le_rpow hbase hs.le
  have hpow_pos : 0 < (n + 1 : ℝ) ^ s := by
    exact Real.rpow_pos_of_pos (by positivity) s
  have hrecip : 1 / ((n + 1 : ℝ) ^ s) ≤ 1 := by
    simpa using
      (one_div_le_one_div hpow_pos (show (0 : ℝ) < 1 by positivity)).2 hpow_ge_one
  simpa using hrecip

lemma tsum_bitProb_ne_top_of_one_lt {s : ℝ} (hs : 1 < s) :
    (∑' n, bitProb s n) ≠ ∞ := by
  have hsumm : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ s) :=
    (Real.summable_one_div_nat_add_rpow 1 s).2 hs
  have hsumm' : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ s)) := by
    refine hsumm.congr ?_
    intro n
    have hnonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    rw [abs_of_nonneg hnonneg]
  simpa [bitProb] using hsumm'.tsum_ofReal_ne_top

lemma tsum_bitProb_eq_top_of_le_one {s : ℝ} (hs : 0 < s) (h_le : s ≤ 1) :
    (∑' n, bitProb s n) = ∞ := by
  by_contra hfinite
  have hsumm : Summable (fun n : ℕ => (bitProb s n).toReal) :=
    ENNReal.summable_toReal hfinite
  have hsumm' : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ s) := by
    refine hsumm.congr ?_
    intro n
    have hnonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    rw [bitProb, ENNReal.toReal_ofReal (by positivity), abs_of_nonneg hnonneg]
  have h_gt : 1 < s := (Real.summable_one_div_nat_add_rpow 1 s).1 hsumm'
  exact (not_lt_of_ge h_le h_gt).elim



theorem ex_5_4_3 {s : ℝ} (hs : 0 < s) :
    (((∑' n, bitProb s n) ≠ ∞) →
        bitStreamMeasure (bitProb s) (limsup oneEvent atTop) = 0) ∧
      (((∑' n, bitProb s n) = ∞) →
        bitStreamMeasure (bitProb s) (limsup oneEvent atTop) = 1) ∧
      ((s ≤ 1) →
        bitStreamMeasure (bitProb s) (limsup oneEvent atTop) = 1) ∧
      ((1 < s) →
        bitStreamMeasure (bitProb s) (limsup oneEvent atTop) = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hfinite
    exact finitely_many_ones_ae_of_tsum_ne_top (bitProb s) (bitProb_le_one hs) hfinite
  · intro hdiv
    exact infinitely_many_ones_ae_of_tsum_eq_top (bitProb s) (bitProb_le_one hs) hdiv
  · intro h_le
    exact infinitely_many_ones_ae_of_tsum_eq_top
      (bitProb s) (bitProb_le_one hs) (tsum_bitProb_eq_top_of_le_one hs h_le)
  · intro h_gt
    exact finitely_many_ones_ae_of_tsum_ne_top
      (bitProb s) (bitProb_le_one hs) (tsum_bitProb_ne_top_of_one_lt h_gt)

end RandomBits
