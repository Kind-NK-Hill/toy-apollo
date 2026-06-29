/-
TASK ID: prob_5_6
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

set_option maxHeartbeats 500000

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators

def prob_5_6_successBlock {Ω : Type*} (success : ℕ → Set Ω) (n k : ℕ) : Set Ω :=
  {ω | ∀ i < n, ω ∈ success (k + i)}

private def prob_5_6_blockIndexSet (n k : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => k + i)

private lemma prob_5_6_successBlock_eq_iInter_range {Ω : Type*}
    (success : ℕ → Set Ω) (n k : ℕ) :
    prob_5_6_successBlock success n k = ⋂ i ∈ Finset.range n, success (k + i) := by
  ext ω
  simp [prob_5_6_successBlock]

private lemma prob_5_6_successBlock_eq_iInter_indexSet {Ω : Type*}
    (success : ℕ → Set Ω) (n k : ℕ) :
    prob_5_6_successBlock success n k =
      ⋂ x ∈ (prob_5_6_blockIndexSet n k : Set ℕ), success x := by
  ext ω
  simp [prob_5_6_successBlock, prob_5_6_blockIndexSet]

private lemma prob_5_6_successBlock_measurableSet {Ω : Type*} [MeasurableSpace Ω]
    (success : ℕ → Set Ω) (h_success_meas : ∀ k, MeasurableSet (success k))
    (n k : ℕ) :
    MeasurableSet (prob_5_6_successBlock success n k) := by
  simpa [prob_5_6_successBlock, Set.setOf_forall] using
    (MeasurableSet.iInter fun i =>
      MeasurableSet.iInter fun _hi : i < n => h_success_meas (k + i))

private lemma prob_5_6_successBlock_measure_prod {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (success : ℕ → Set Ω) (n k : ℕ)
    (h_success_indep : iIndepSet success P) :
    P (prob_5_6_successBlock success n k) =
      ∏ x ∈ prob_5_6_blockIndexSet n k, P (success x) := by
  rw [prob_5_6_successBlock_eq_iInter_indexSet]
  exact h_success_indep.meas_biInter (prob_5_6_blockIndexSet n k)

private lemma prob_5_6_successBlock_measure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (alpha : ℝ) (success : ℕ → Set Ω) (n k : ℕ)
    (h_success_prob :
      ∀ k : ℕ, P (success k) = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) ^ (-alpha)))
    (h_success_indep : iIndepSet success P) :
    P (prob_5_6_successBlock success n k) =
      ∏ i ∈ Finset.range n,
        ENNReal.ofReal ((((k + i) + 1 : ℕ) : ℝ) ^ (-alpha)) := by
  rw [prob_5_6_successBlock_eq_iInter_range]
  calc
    P (⋂ i ∈ Finset.range n, success (k + i))
        = P (⋂ x ∈ (Finset.range n).image (fun i => k + i), success x) := by
          congr 1
          ext ω
          simp
    _ = ∏ x ∈ (Finset.range n).image (fun i => k + i), P (success x) := by
          exact h_success_indep.meas_biInter ((Finset.range n).image (fun i => k + i))
    _ = ∏ i ∈ Finset.range n, P (success (k + i)) := by
          rw [Finset.prod_image]
          intro a _ha b _hb hab
          exact Nat.add_left_cancel hab
    _ = ∏ i ∈ Finset.range n,
          ENNReal.ofReal ((((k + i) + 1 : ℕ) : ℝ) ^ (-alpha)) := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          exact h_success_prob (k + i)

private lemma prob_5_6_prod_rpow_upper {alpha : ℝ} (h_alpha_pos : 0 < alpha)
    (n k : ℕ) :
    ∏ i ∈ Finset.range n, ((((k + i) + 1 : ℕ) : ℝ) ^ (-alpha)) ≤
      (((k + 1 : ℕ) : ℝ) ^ (-((n : ℝ) * alpha))) := by
  calc
    ∏ i ∈ Finset.range n, ((((k + i) + 1 : ℕ) : ℝ) ^ (-alpha))
        ≤ ∏ _i ∈ Finset.range n, (((k + 1 : ℕ) : ℝ) ^ (-alpha)) := by
          refine Finset.prod_le_prod (fun i hi => by positivity) ?_
          intro i _hi
          have hbase : (((k + 1 : ℕ) : ℝ) ≤ (((k + i) + 1 : ℕ) : ℝ)) := by
            norm_cast
            omega
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
    _ = (((k + 1 : ℕ) : ℝ) ^ (-alpha)) ^ n := by
          simp
    _ = (((k + 1 : ℕ) : ℝ) ^ (-((n : ℝ) * alpha))) := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul (by positivity)]
          ring_nf

private lemma prob_5_6_blocks_tsum_ne_top {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (alpha : ℝ) (h_alpha_pos : 0 < alpha)
    (n : ℕ) (success : ℕ → Set Ω)
    (h_success_prob :
      ∀ k : ℕ, P (success k) = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) ^ (-alpha)))
    (h_success_indep : iIndepSet success P)
    (h : 1 < (n : ℝ) * alpha) :
    (∑' k, P (prob_5_6_successBlock success n k)) ≠ ∞ := by
  have h_upper : ∀ k, P (prob_5_6_successBlock success n k) ≤
      ENNReal.ofReal ((((k + 1 : ℕ) : ℝ) ^ (-((n : ℝ) * alpha)))) := by
    intro k
    rw [prob_5_6_successBlock_measure P alpha success n k h_success_prob h_success_indep]
    rw [← ENNReal.ofReal_prod_of_nonneg]
    · exact ENNReal.ofReal_le_ofReal (prob_5_6_prod_rpow_upper h_alpha_pos n k)
    · intro i _hi
      positivity
  have h_summable_upper :
      Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ) ^ (-((n : ℝ) * alpha)))) := by
    have hs : Summable (fun k : ℕ => ((k : ℝ) ^ (-((n : ℝ) * alpha)))) := by
      exact Real.summable_nat_rpow.2 (by linarith)
    simpa [Nat.cast_add, Nat.cast_one] using ((summable_nat_add_iff 1).2 hs)
  exact ne_top_of_le_ne_top h_summable_upper.tsum_ofReal_ne_top
    (ENNReal.tsum_le_tsum h_upper)

private lemma prob_5_6_nat_block_bound {n : ℕ} (j : ℕ) {i : ℕ} (hi : i < n) :
    j * n + i + 1 ≤ (j + 1) * n := by
  nlinarith

private lemma prob_5_6_prod_rpow_lower {alpha : ℝ} (h_alpha_pos : 0 < alpha)
    {n : ℕ} (hn : 0 < n) (j : ℕ) :
    (((j + 1) * n : ℕ) : ℝ) ^ (-((n : ℝ) * alpha)) ≤
      ∏ i ∈ Finset.range n, (((j * n + i + 1 : ℕ) : ℝ) ^ (-alpha)) := by
  calc
    (((j + 1) * n : ℕ) : ℝ) ^ (-((n : ℝ) * alpha))
        = ((((j + 1) * n : ℕ) : ℝ) ^ (-alpha)) ^ n := by
          rw [← Real.rpow_natCast]
          rw [← Real.rpow_mul (by positivity)]
          ring_nf
    _ = ∏ _i ∈ Finset.range n, ((((j + 1) * n : ℕ) : ℝ) ^ (-alpha)) := by
          simp
    _ ≤ ∏ i ∈ Finset.range n, (((j * n + i + 1 : ℕ) : ℝ) ^ (-alpha)) := by
          refine Finset.prod_le_prod (fun i hi => by positivity) ?_
          intro i hi
          have hi_lt : i < n := Finset.mem_range.mp hi
          have hbase_nat : j * n + i + 1 ≤ (j + 1) * n :=
            prob_5_6_nat_block_bound j hi_lt
          have hbase : (((j * n + i + 1 : ℕ) : ℝ) ≤ (((j + 1) * n : ℕ) : ℝ)) := by
            exact_mod_cast hbase_nat
          exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)

private lemma prob_5_6_lower_not_summable {alpha : ℝ}
    {n : ℕ} (hn : 0 < n) (h : (n : ℝ) * alpha ≤ 1) :
    ¬ Summable (fun j : ℕ => (((j + 1) * n : ℕ) : ℝ) ^
      (-((n : ℝ) * alpha))) := by
  intro hs_lower
  let p : ℝ := (n : ℝ) * alpha
  have hconst_ne : ((n : ℝ) ^ (-p)) ≠ 0 := by
    positivity
  have hs_lower_p :
      Summable (fun j : ℕ => (((j + 1) * n : ℕ) : ℝ) ^ (-p)) := by
    simpa [p] using hs_lower
  have h_eq : (fun j : ℕ => (((j + 1) * n : ℕ) : ℝ) ^ (-p)) =
      fun j : ℕ => (((j + 1 : ℕ) : ℝ) ^ (-p)) * ((n : ℝ) ^ (-p)) := by
    funext j
    have hcast : (((j + 1) * n : ℕ) : ℝ) =
        (((j + 1 : ℕ) : ℝ) * (n : ℝ)) := by
      norm_num
    rw [hcast]
    rw [Real.mul_rpow (by positivity) (by positivity)]
  have hs_shift_mul :
      Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ) ^ (-p)) * ((n : ℝ) ^ (-p))) := by
    simpa only [h_eq] using hs_lower_p
  have hs_shift : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ) ^ (-p))) :=
    (summable_mul_right_iff hconst_ne).1 hs_shift_mul
  have hs_all : Summable (fun k : ℕ => ((k : ℝ) ^ (-p))) := by
    exact (summable_nat_add_iff (f := fun k : ℕ => ((k : ℝ) ^ (-p))) 1).1 hs_shift
  have hp_lt : -p < -1 := Real.summable_nat_rpow.1 hs_all
  linarith

private lemma prob_5_6_subseq_tsum_eq_top {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (alpha : ℝ) (h_alpha_pos : 0 < alpha)
    (n : ℕ) (hn : 0 < n) (success : ℕ → Set Ω)
    (h_success_prob :
      ∀ k : ℕ, P (success k) = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) ^ (-alpha)))
    (h_success_indep : iIndepSet success P)
    (h : (n : ℝ) * alpha ≤ 1) :
    (∑' j, P (prob_5_6_successBlock success n (j * n))) = ∞ := by
  by_contra h_ne
  have h_tsum_ne_top :
      (∑' j, P (prob_5_6_successBlock success n (j * n))) ≠ ∞ := h_ne
  have h_toReal_summable :
      Summable (fun j : ℕ => (P (prob_5_6_successBlock success n (j * n))).toReal) :=
    ENNReal.summable_toReal h_tsum_ne_top
  have h_lower_real : ∀ j : ℕ,
      (((j + 1) * n : ℕ) : ℝ) ^ (-((n : ℝ) * alpha)) ≤
        (P (prob_5_6_successBlock success n (j * n))).toReal := by
    intro j
    have h_lower_enn :
        ENNReal.ofReal ((((j + 1) * n : ℕ) : ℝ) ^ (-((n : ℝ) * alpha))) ≤
          P (prob_5_6_successBlock success n (j * n)) := by
      rw [prob_5_6_successBlock_measure P alpha success n (j * n)
        h_success_prob h_success_indep]
      rw [← ENNReal.ofReal_prod_of_nonneg]
      · exact ENNReal.ofReal_le_ofReal (prob_5_6_prod_rpow_lower h_alpha_pos hn j)
      · intro i _hi
        positivity
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top P _)).1 h_lower_enn
  have h_lower_summable :
      Summable (fun j : ℕ => (((j + 1) * n : ℕ) : ℝ) ^
        (-((n : ℝ) * alpha))) :=
    Summable.of_nonneg_of_le (fun j => by positivity) h_lower_real h_toReal_summable
  exact prob_5_6_lower_not_summable hn h h_lower_summable

private lemma prob_5_6_indexSet_eq_of_mem {n a b x : ℕ}
    (hxa : x ∈ prob_5_6_blockIndexSet n (a * n))
    (hxb : x ∈ prob_5_6_blockIndexSet n (b * n)) : a = b := by
  rcases Finset.mem_image.mp hxa with ⟨i, hi, rfl⟩
  rcases Finset.mem_image.mp hxb with ⟨l, hl, hEq⟩
  have hi_lt : i < n := Finset.mem_range.mp hi
  have hl_lt : l < n := Finset.mem_range.mp hl
  nlinarith

private lemma prob_5_6_successBlock_subseq_inter_eq {Ω : Type*}
    (success : ℕ → Set Ω) (n : ℕ) (s : Finset ℕ) :
    (⋂ j ∈ (s : Set ℕ), prob_5_6_successBlock success n (j * n)) =
      ⋂ x ∈ ((s.biUnion (fun j => prob_5_6_blockIndexSet n (j * n)) : Finset ℕ) : Set ℕ),
        success x := by
  ext ω
  simp [prob_5_6_successBlock, prob_5_6_blockIndexSet]

private lemma prob_5_6_subseq_blocks_indep {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (n : ℕ) (success : ℕ → Set Ω)
    (h_success_meas : ∀ k, MeasurableSet (success k))
    (h_success_indep : iIndepSet success P) :
    iIndepSet (fun j => prob_5_6_successBlock success n (j * n)) P := by
  rw [ProbabilityTheory.iIndepSet_iff_meas_biInter
    (fun j => prob_5_6_successBlock_measurableSet success h_success_meas n (j * n))]
  intro s
  have hdisj :
      (s : Set ℕ).PairwiseDisjoint (fun j => prob_5_6_blockIndexSet n (j * n)) := by
    intro a _ha b _hb hab
    change Disjoint (prob_5_6_blockIndexSet n (a * n))
      (prob_5_6_blockIndexSet n (b * n))
    rw [Finset.disjoint_left]
    intro x hxa hxb
    exact hab (prob_5_6_indexSet_eq_of_mem hxa hxb)
  calc
    P (⋂ j ∈ (s : Set ℕ), prob_5_6_successBlock success n (j * n))
        = P (⋂ x ∈
            ((s.biUnion (fun j => prob_5_6_blockIndexSet n (j * n)) : Finset ℕ) : Set ℕ),
              success x) := by
          rw [prob_5_6_successBlock_subseq_inter_eq]
    _ = ∏ x ∈ s.biUnion (fun j => prob_5_6_blockIndexSet n (j * n)), P (success x) := by
          exact h_success_indep.meas_biInter
            (s.biUnion (fun j => prob_5_6_blockIndexSet n (j * n)))
    _ = ∏ j ∈ (s : Finset ℕ),
          ∏ x ∈ prob_5_6_blockIndexSet n (j * n), P (success x) := by
          rw [Finset.prod_biUnion hdisj]
    _ = ∏ j ∈ (s : Finset ℕ), P (prob_5_6_successBlock success n (j * n)) := by
          refine Finset.prod_congr rfl ?_
          intro j _hj
          exact (prob_5_6_successBlock_measure_prod P success n (j * n) h_success_indep).symm

private lemma prob_5_6_limsup_subseq_subset {Ω : Type*} (success : ℕ → Set Ω)
    {n : ℕ} (hn : 0 < n) :
    limsup (fun j => prob_5_6_successBlock success n (j * n)) atTop ⊆
      limsup (fun k => prob_5_6_successBlock success n k) atTop := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat, Filter.limsup_eq_iInf_iSup_of_nat]
  simp [Set.subset_def]
  intro ω hω N
  obtain ⟨j, hj, hmem⟩ := hω N
  refine ⟨j * n, ?_, hmem⟩
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
  have hj_le : j ≤ j * n := by
    nth_rewrite 1 [← Nat.mul_one j]
    exact Nat.mul_le_mul_left j hn1
  exact le_trans hj hj_le

theorem prob_5_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (alpha : ℝ) (h_alpha_pos : 0 < alpha) (_h_alpha_lt_one : alpha < 1)
    (n : ℕ) (hn : 0 < n)
    (success : ℕ → Set Ω)
    (h_success_meas : ∀ k, MeasurableSet (success k))
    (h_success_prob :
      ∀ k : ℕ, P (success k) = ENNReal.ofReal (((k + 1 : ℕ) : ℝ) ^ (-alpha)))
    (h_success_indep : iIndepSet success P) :
    P (limsup (fun k => prob_5_6_successBlock success n k) atTop) =
      if (n : ℝ) * alpha ≤ 1 then 1 else 0 := by
  by_cases hcase : (n : ℝ) * alpha ≤ 1
  · simp [hcase]
    have h_meas_subseq :
        ∀ j, MeasurableSet (prob_5_6_successBlock success n (j * n)) :=
      fun j => prob_5_6_successBlock_measurableSet success h_success_meas n (j * n)
    have h_subseq_one :
        P (limsup (fun j => prob_5_6_successBlock success n (j * n)) atTop) = 1 := by
      exact ProbabilityTheory.measure_limsup_eq_one
        (μ := P)
        (hsm := h_meas_subseq)
        (hs := prob_5_6_subseq_blocks_indep P n success h_success_meas h_success_indep)
        (hs' := prob_5_6_subseq_tsum_eq_top P alpha h_alpha_pos n hn success
          h_success_prob h_success_indep hcase)
    · have h_subset := prob_5_6_limsup_subseq_subset success hn
      have h_mono :
          P (limsup (fun j => prob_5_6_successBlock success n (j * n)) atTop) ≤
            P (limsup (fun k => prob_5_6_successBlock success n k) atTop) :=
        measure_mono h_subset
      have h_lower :
          (1 : ℝ≥0∞) ≤ P (limsup (fun k => prob_5_6_successBlock success n k) atTop) := by
        simpa [h_subseq_one] using h_mono
      have h_upper :
          P (limsup (fun k => prob_5_6_successBlock success n k) atTop) ≤ 1 := by
        have h_upper_univ :
            P (limsup (fun k => prob_5_6_successBlock success n k) atTop) ≤
              P (Set.univ : Set Ω) :=
          measure_mono (Set.subset_univ _)
        simpa [measure_univ] using h_upper_univ
      exact le_antisymm h_upper h_lower
  · simp [hcase]
    have hgt : 1 < (n : ℝ) * alpha := lt_of_not_ge hcase
    exact MeasureTheory.measure_limsup_atTop_eq_zero
      (μ := P)
      (s := fun k => prob_5_6_successBlock success n k)
      (prob_5_6_blocks_tsum_ne_top P alpha h_alpha_pos n success
        h_success_prob h_success_indep hgt)
