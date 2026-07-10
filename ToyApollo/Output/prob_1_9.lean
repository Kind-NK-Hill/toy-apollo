/-
TASK ID: prob_1_9
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_1_2

noncomputable section

structure RSWeakPartition (a b : ℝ) where
  n : ℕ
  pts : ℕ → ℝ
  pts_start : pts 0 = a
  pts_end : pts n = b
  mono : ∀ i, i < n → pts i ≤ pts (i + 1)

namespace RSWeakPartition

def TagsIn {a b : ℝ} (Q : RSWeakPartition a b) (tags : ℕ → ℝ) : Prop :=
  ∀ i, i < Q.n → tags i ∈ Set.Icc (Q.pts i) (Q.pts (i + 1))

def taggedSum {a b : ℝ} (Q : RSWeakPartition a b) (tags : ℕ → ℝ)
    (f α : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range Q.n,
    f (tags i) * (α (Q.pts (i + 1)) - α (Q.pts i))

theorem zero_cell_term {a b : ℝ} (Q : RSWeakPartition a b) (tags : ℕ → ℝ)
    (f α : ℝ → ℝ) {i : ℕ} (hzero : Q.pts i = Q.pts (i + 1)) :
    f (tags i) * (α (Q.pts (i + 1)) - α (Q.pts i)) = 0 := by
  simp [hzero]

theorem taggedSum_filter_nonzero_cells {a b : ℝ} (Q : RSWeakPartition a b)
    (tags : ℕ → ℝ) (f α : ℝ → ℝ) :
    taggedSum Q tags f α =
      ∑ i ∈ (Finset.range Q.n).filter (fun i => Q.pts i ≠ Q.pts (i + 1)),
        f (tags i) * (α (Q.pts (i + 1)) - α (Q.pts i)) := by
  classical
  unfold taggedSum
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hzero : Q.pts i = Q.pts (i + 1)
  · simp [hzero]
  · simp [hzero]

theorem endpoint_product_telescope {f α : ℝ → ℝ} {a b : ℝ}
    (Q : RSWeakPartition a b) :
    f b * α b - f a * α a =
      ∑ i ∈ Finset.range Q.n,
        (f (Q.pts (i + 1)) * α (Q.pts (i + 1)) -
          f (Q.pts i) * α (Q.pts i)) := by
  let g : ℕ → ℝ := fun i => f (Q.pts i) * α (Q.pts i)
  calc
    f b * α b - f a * α a = g Q.n - g 0 := by
      simp [g, Q.pts_start, Q.pts_end]
    _ = ∑ i ∈ Finset.range Q.n, (g (i + 1) - g i) := by
      exact (Finset.sum_range_sub g Q.n).symm
    _ =
        ∑ i ∈ Finset.range Q.n,
          (f (Q.pts (i + 1)) * α (Q.pts (i + 1)) -
            f (Q.pts i) * α (Q.pts i)) := by
      rfl

end RSWeakPartition

private lemma prob_1_9_sum_adjacent_sub {n : ℕ} (g : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (g i.succ - g i.castSucc)) =
      g (Fin.last n) - g 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have htail := ih (fun i : Fin (n + 1) => g i.succ)
      have htail' :
          (∑ i : Fin n, (g i.succ.succ - g i.succ.castSucc)) =
            g (Fin.last n).succ - g (Fin.succ 0) := by
        simpa only [Fin.succ_castSucc] using htail
      rw [htail']
      simp

theorem prob_1_9_endpoint_product_telescope {f α : ℝ → ℝ} {a b : ℝ}
    (P : RSPartition a b) :
    f b * α b - f a * α a =
      ∑ i : Fin P.n,
        (f (P.pts i.succ) * α (P.pts i.succ) -
          f (P.pts i.castSucc) * α (P.pts i.castSucc)) := by
  have hsum := prob_1_9_sum_adjacent_sub
    (fun i : Fin (P.n + 1) => f (P.pts i) * α (P.pts i))
  simpa [P.pts_start, P.pts_end] using hsum.symm

theorem prob_1_9_rightTagsInPartition {a b : ℝ} (P : RSPartition a b) :
    DarbouxRS.tagsInPartition P (fun i => P.pts i.succ) := by
  intro i
  exact ⟨le_of_lt (P.strict_mono Fin.castSucc_lt_succ), le_rfl⟩

theorem prob_1_9_endpoint_split_telescope {f α : ℝ → ℝ} {a b : ℝ}
    (P : RSPartition a b) :
    f b * α b - f a * α a =
      DarbouxRS.taggedSum P (fun i => P.pts i.succ) f α +
        DarbouxRS.taggedSum P (fun i => P.pts i.castSucc) α f := by
  rw [prob_1_9_endpoint_product_telescope (f := f) (α := α) (P := P)]
  unfold DarbouxRS.taggedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem prob_1_9_refined_sum_algebra {f α : ℝ → ℝ} {a b : ℝ}
    (P : RSPartition a b) (tags : Fin P.n → ℝ) :
    f b * α b - f a * α a - DarbouxRS.taggedSum P tags α f =
      ∑ i : Fin P.n,
        (f (P.pts i.castSucc) * (α (tags i) - α (P.pts i.castSucc)) +
          f (P.pts i.succ) * (α (P.pts i.succ) - α (tags i))) := by
  rw [prob_1_9_endpoint_product_telescope (P := P)]
  unfold DarbouxRS.taggedSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

private def prob_1_9_partitionPointNat {a b : ℝ}
    (P : RSPartition a b) (k : ℕ) : ℝ :=
  if hk : k ≤ P.n then P.pts ⟨k, Nat.lt_succ_iff.mpr hk⟩ else b

private theorem prob_1_9_partitionPointNat_fin {a b : ℝ}
    (P : RSPartition a b) (k : Fin (P.n + 1)) :
    prob_1_9_partitionPointNat P k = P.pts k := by
  simp [prob_1_9_partitionPointNat, Nat.le_of_lt_succ k.isLt]

private theorem prob_1_9_partitionPointNat_of_le {a b : ℝ}
    (P : RSPartition a b) {k : ℕ} (hk : k ≤ P.n) :
    prob_1_9_partitionPointNat P k =
      P.pts ⟨k, Nat.lt_succ_iff.mpr hk⟩ := by
  simp [prob_1_9_partitionPointNat, hk]

private def prob_1_9_tagNat {a b : ℝ} (P : RSPartition a b)
    (tags : Fin P.n → ℝ) (k : ℕ) : ℝ :=
  if hk : k < P.n then tags ⟨k, hk⟩ else b

private theorem prob_1_9_tagNat_of_lt {a b : ℝ} (P : RSPartition a b)
    (tags : Fin P.n → ℝ) {k : ℕ} (hk : k < P.n) :
    prob_1_9_tagNat P tags k = tags ⟨k, hk⟩ := by
  simp [prob_1_9_tagNat, hk]

noncomputable def prob_1_9_refinedWeakPartition {a b : ℝ}
    (P : RSPartition a b) (tags : Fin P.n → ℝ)
    (htags : DarbouxRS.tagsInPartition P tags) : RSWeakPartition a b where
  n := 2 * P.n
  pts := fun j =>
    if j % 2 = 0 then prob_1_9_partitionPointNat P (j / 2)
    else prob_1_9_tagNat P tags (j / 2)
  pts_start := by
    rw [prob_1_9_partitionPointNat_of_le P (Nat.zero_le P.n)]
    exact P.pts_start
  pts_end := by
    have hmod : (2 * P.n) % 2 = 0 := by omega
    have hdiv : (2 * P.n) / 2 = P.n := by omega
    simp only [hmod, if_pos, hdiv]
    rw [prob_1_9_partitionPointNat_of_le P le_rfl]
    exact P.pts_end
  mono := by
    intro j hj
    by_cases heven : j % 2 = 0
    · have hodd_next : (j + 1) % 2 ≠ 0 := by omega
      have hhalf_next : (j + 1) / 2 = j / 2 := by omega
      have hj_half_lt : j / 2 < P.n := by omega
      let i : Fin P.n := ⟨j / 2, hj_half_lt⟩
      have htag := htags i
      simp only [heven, if_pos, hodd_next, hhalf_next]
      rw [prob_1_9_partitionPointNat_of_le P (Nat.le_of_lt hj_half_lt)]
      rw [prob_1_9_tagNat_of_lt P tags hj_half_lt]
      simpa [i] using htag.1
    · have hnext_even : (j + 1) % 2 = 0 := by omega
      have hhalf_next : (j + 1) / 2 = j / 2 + 1 := by omega
      have hj_half_lt : j / 2 < P.n := by omega
      let i : Fin P.n := ⟨j / 2, hj_half_lt⟩
      have htag := htags i
      simp only [heven, hnext_even, if_pos, hhalf_next]
      rw [prob_1_9_tagNat_of_lt P tags hj_half_lt]
      rw [prob_1_9_partitionPointNat_of_le P (Nat.succ_le_of_lt hj_half_lt)]
      simpa [i] using htag.2

noncomputable def prob_1_9_refinedWeakTags {a b : ℝ}
    (P : RSPartition a b) : ℕ → ℝ :=
  fun j =>
    if j % 2 = 0 then prob_1_9_partitionPointNat P (j / 2)
    else prob_1_9_partitionPointNat P (j / 2 + 1)

theorem prob_1_9_refinedWeakTagsIn {a b : ℝ}
    (P : RSPartition a b) (tags : Fin P.n → ℝ)
    (htags : DarbouxRS.tagsInPartition P tags) :
    RSWeakPartition.TagsIn
      (prob_1_9_refinedWeakPartition P tags htags)
      (prob_1_9_refinedWeakTags P) := by
  intro j hj
  have hj' : j < 2 * P.n := by
    simpa [prob_1_9_refinedWeakPartition] using hj
  by_cases heven : j % 2 = 0
  · have hodd_next : (j + 1) % 2 ≠ 0 := by omega
    have hhalf_next : (j + 1) / 2 = j / 2 := by omega
    have hj_half_lt : j / 2 < P.n := by omega
    let i : Fin P.n := ⟨j / 2, hj_half_lt⟩
    have htag := htags i
    simp only [prob_1_9_refinedWeakPartition, prob_1_9_refinedWeakTags,
      heven, if_pos, hodd_next, hhalf_next]
    rw [prob_1_9_partitionPointNat_of_le P (Nat.le_of_lt hj_half_lt)]
    rw [prob_1_9_tagNat_of_lt P tags hj_half_lt]
    simpa [i] using htag.1
  · have hnext_even : (j + 1) % 2 = 0 := by omega
    have hhalf_next : (j + 1) / 2 = j / 2 + 1 := by omega
    have hj_half_lt : j / 2 < P.n := by omega
    let i : Fin P.n := ⟨j / 2, hj_half_lt⟩
    have htag := htags i
    simp only [prob_1_9_refinedWeakPartition, prob_1_9_refinedWeakTags,
      heven, hnext_even, if_pos, hhalf_next]
    rw [prob_1_9_tagNat_of_lt P tags hj_half_lt]
    rw [prob_1_9_partitionPointNat_of_le P (Nat.succ_le_of_lt hj_half_lt)]
    simpa [i] using htag.2

private theorem prob_1_9_sum_range_two_mul {β : Type*} [AddCommMonoid β]
    (n : ℕ) (g : ℕ → β) :
    (∑ j ∈ Finset.range (2 * n), g j) =
      ∑ i ∈ Finset.range n, (g (2 * i) + g (2 * i + 1)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        (∑ j ∈ Finset.range (2 * (n + 1)), g j)
            = ∑ j ∈ Finset.range (2 * n + 2), g j := by
              congr 2
        _ = (∑ j ∈ Finset.range (2 * n), g j) + g (2 * n) + g (2 * n + 1) := by
              rw [Finset.sum_range_succ, Finset.sum_range_succ]
        _ = (∑ i ∈ Finset.range n, (g (2 * i) + g (2 * i + 1))) +
              g (2 * n) + g (2 * n + 1) := by
              rw [ih]
        _ = ∑ i ∈ Finset.range (n + 1), (g (2 * i) + g (2 * i + 1)) := by
              rw [Finset.sum_range_succ]
              ac_rfl

theorem prob_1_9_refined_sum_as_weak_taggedSum {f α : ℝ → ℝ} {a b : ℝ}
    (P : RSPartition a b) (tags : Fin P.n → ℝ)
    (htags : DarbouxRS.tagsInPartition P tags) :
    f b * α b - f a * α a - DarbouxRS.taggedSum P tags α f =
      RSWeakPartition.taggedSum
        (prob_1_9_refinedWeakPartition P tags htags)
        (prob_1_9_refinedWeakTags P) f α := by
  rw [prob_1_9_refined_sum_algebra (P := P) (tags := tags)]
  unfold RSWeakPartition.taggedSum
  let originalTermNat : ℕ → ℝ := fun i =>
    f (prob_1_9_partitionPointNat P i) *
        (α (prob_1_9_tagNat P tags i) - α (prob_1_9_partitionPointNat P i)) +
      f (prob_1_9_partitionPointNat P (i + 1)) *
        (α (prob_1_9_partitionPointNat P (i + 1)) - α (prob_1_9_tagNat P tags i))
  have horiginal :
      (∑ i : Fin P.n,
        (f (P.pts i.castSucc) * (α (tags i) - α (P.pts i.castSucc)) +
          f (P.pts i.succ) * (α (P.pts i.succ) - α (tags i)))) =
        ∑ i ∈ Finset.range P.n, originalTermNat i := by
    calc
      (∑ i : Fin P.n,
        (f (P.pts i.castSucc) * (α (tags i) - α (P.pts i.castSucc)) +
          f (P.pts i.succ) * (α (P.pts i.succ) - α (tags i)))) =
          ∑ i : Fin P.n, originalTermNat i.val := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            dsimp [originalTermNat]
            rw [prob_1_9_partitionPointNat_of_le P (Nat.le_of_lt i.isLt)]
            rw [prob_1_9_partitionPointNat_of_le P (Nat.succ_le_of_lt i.isLt)]
            rw [prob_1_9_tagNat_of_lt P tags i.isLt]
            congr 4
      _ = ∑ i ∈ Finset.range P.n, originalTermNat i :=
        Fin.sum_univ_eq_sum_range originalTermNat P.n
  rw [horiginal]
  change
    (∑ i ∈ Finset.range P.n, originalTermNat i) =
      ∑ j ∈ Finset.range (2 * P.n),
        f (prob_1_9_refinedWeakTags P j) *
          (α ((prob_1_9_refinedWeakPartition P tags htags).pts (j + 1)) -
            α ((prob_1_9_refinedWeakPartition P tags htags).pts j))
  rw [prob_1_9_sum_range_two_mul P.n]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  let fi : Fin P.n := ⟨i, hi_lt⟩
  have h2i : (2 * i) % 2 = 0 := by omega
  have h2idiv : (2 * i) / 2 = i := by omega
  have h2i1 : (2 * i + 1) % 2 ≠ 0 := by omega
  have h2i1div : (2 * i + 1) / 2 = i := by omega
  have h2i2 : (2 * i + 1 + 1) % 2 = 0 := by omega
  have h2i2div : (2 * i + 1 + 1) / 2 = i + 1 := by omega
  simp [originalTermNat, prob_1_9_refinedWeakPartition, prob_1_9_refinedWeakTags,
    h2i, h2idiv, h2i1div, h2i2, h2i2div]

theorem prob_1_9 {f α : ℝ → ℝ} {a b : ℝ}
    (_hab : a ≤ b)
    (_hfmono : MonotoneOn f (Set.Icc a b))
    (_hαmono : MonotoneOn α (Set.Icc a b))
    (hfα : RSIntegrable f α a b)
    (hαf : RSIntegrable α f a b) :
    rsIntegral α f a b hαf =
      f b * α b - f a * α a - rsIntegral f α a b hfα := by
  let Ifα := rsIntegral f α a b hfα
  let Iαf := rsIntegral α f a b hαf
  let C := f b * α b - f a * α a
  have hsum : Ifα + Iαf = C := by
    rcases (rsIntegral_spec hfα) with ⟨hsource_fα, hlim_fα⟩
    rcases (rsIntegral_spec hαf) with ⟨_hsource_αf, hlim_αf⟩
    rcases hsource_fα with ⟨hablt, _hbddAbove_fα, _hbddBelow_fα, _hmonoα⟩
    refine eq_of_forall_dist_le ?_
    intro eps heps
    have hhalf : 0 < eps / 2 := half_pos heps
    rcases hlim_fα (eps / 2) hhalf with ⟨δfα, hδfα, Hfα⟩
    rcases hlim_αf (eps / 2) hhalf with ⟨δαf, hδαf, Hαf⟩
    rcases DarbouxRS.exists_partition_mesh_lt hablt (lt_min hδfα hδαf) with
      ⟨P, hPmesh⟩
    let rightTags : Fin P.n → ℝ := fun i => P.pts i.succ
    let leftTags : Fin P.n → ℝ := fun i => P.pts i.castSucc
    have hmesh_fα : P.mesh < δfα := lt_of_lt_of_le hPmesh (min_le_left δfα δαf)
    have hmesh_αf : P.mesh < δαf := lt_of_lt_of_le hPmesh (min_le_right δfα δαf)
    have hright : DarbouxRS.tagsInPartition P rightTags := by
      dsimp [rightTags]
      exact prob_1_9_rightTagsInPartition P
    have hleft : DarbouxRS.tagsInPartition P leftTags := by
      dsimp [leftTags]
      exact DarbouxRS.leftTagsInPartition P
    have hRfα := Hfα P rightTags hright hmesh_fα
    have hLαf := Hαf P leftTags hleft hmesh_αf
    have hsplit :
        C =
          DarbouxRS.taggedSum P rightTags f α +
            DarbouxRS.taggedSum P leftTags α f := by
      dsimp [C, rightTags, leftTags]
      exact prob_1_9_endpoint_split_telescope (f := f) (α := α) (P := P)
    have hdecomp :
        Ifα + Iαf - C =
          - (DarbouxRS.taggedSum P rightTags f α - Ifα) -
            (DarbouxRS.taggedSum P leftTags α f - Iαf) := by
      rw [hsplit]
      ring
    have hlt : |Ifα + Iαf - C| < eps := by
      calc
        |Ifα + Iαf - C| =
            |- (DarbouxRS.taggedSum P rightTags f α - Ifα) -
              (DarbouxRS.taggedSum P leftTags α f - Iαf)| := by
          rw [hdecomp]
        _ ≤
            |-(DarbouxRS.taggedSum P rightTags f α - Ifα)| +
              |-(DarbouxRS.taggedSum P leftTags α f - Iαf)| := by
          simpa [sub_eq_add_neg] using
            (abs_add_le
              (-(DarbouxRS.taggedSum P rightTags f α - Ifα))
              (-(DarbouxRS.taggedSum P leftTags α f - Iαf)))
        _ =
            |DarbouxRS.taggedSum P rightTags f α - Ifα| +
              |DarbouxRS.taggedSum P leftTags α f - Iαf| := by
          rw [abs_neg, abs_neg]
        _ < eps := by
          have hsum_lt :
              |DarbouxRS.taggedSum P rightTags f α - Ifα| +
                  |DarbouxRS.taggedSum P leftTags α f - Iαf| <
                eps / 2 + eps / 2 := add_lt_add hRfα hLαf
          simpa using hsum_lt
    have hdist : dist (Ifα + Iαf) C < eps := by
      simpa [Real.dist_eq] using hlt
    exact le_of_lt hdist
  dsimp [Ifα, Iαf, C] at hsum ⊢
  linarith
