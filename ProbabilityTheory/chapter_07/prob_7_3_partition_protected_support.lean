/-
TASK ID: prob_7_3_partition_protected_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_07.prob_7_3_partition_atom_support

open MeasureTheory Set Filter

noncomputable section

theorem prob_7_3_compact_away_point_has_positive_distance
    {K : Set ℝ} {c : ℝ}
    (hKcompact : IsCompact K) (hc : c ∉ K) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, x ∈ K → r ≤ |x - c| := by
  have hOpen : IsOpen Kᶜ := hKcompact.isClosed.isOpen_compl
  have hcCompl : c ∈ Kᶜ := hc
  rcases (Metric.isOpen_iff.mp hOpen c hcCompl) with ⟨r, hr, hball⟩
  refine ⟨r, hr, ?_⟩
  intro x hxK
  have hnotBall : ¬ x ∈ Metric.ball c r := by
    intro hxBall
    exact (hball hxBall) hxK
  have hle_xc : r ≤ dist x c := by
    simpa [Metric.mem_ball] using hnotBall
  have hle : r ≤ dist c x := by
    simpa [dist_comm] using hle_xc
  simpa [Real.dist_eq, abs_sub_comm] using hle

theorem prob_7_3_compact_finite_ball_subcover
    {K : Set ℝ} (hKcompact : IsCompact K)
    (r : ℝ → ℝ) (hr : ∀ x : ℝ, x ∈ K → 0 < r x) :
    ∃ S : Finset ℝ,
      (∀ x ∈ S, x ∈ K) ∧
      K ⊆ ⋃ x ∈ S, Metric.ball x (r x) := by
  exact hKcompact.elim_nhds_subcover
    (fun x : ℝ => Metric.ball x (r x))
    (fun x hx => Metric.ball_mem_nhds x (hr x hx))

theorem prob_7_3_compact_finite_uniform_ball_subcover
    {K : Set ℝ} (hKcompact : IsCompact K) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ S : Finset ℝ,
      (∀ x ∈ S, x ∈ K) ∧
      K ⊆ ⋃ x ∈ S, Metric.ball x ρ := by
  simpa using
    prob_7_3_compact_finite_ball_subcover
      (K := K) hKcompact (fun _ : ℝ => ρ) (fun _ _ => hρ)

theorem prob_7_3_finset_away_point_has_positive_distance
    (T : Finset ℝ) {c : ℝ} (hc : c ∉ T) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, x ∈ T → r ≤ |x - c| := by
  exact prob_7_3_compact_away_point_has_positive_distance
    (K := (T : Set ℝ)) T.finite_toSet.isCompact (by simpa using hc)

theorem prob_7_3_finset_Icc_away_left_has_uniform_endpoint_margins
    {a b : ℝ} (T : Finset ℝ)
    (hT : ∀ x ∈ T, x ∈ Icc a b)
    (haT : a ∉ T) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ x ∈ T, ρ ≤ x - a) ∧
      (∀ x ∈ T, x ≠ b → ρ ≤ b - x) := by
  rcases prob_7_3_finset_away_point_has_positive_distance T haT with
    ⟨ρL, hρL, hleftDist⟩
  have hbErase : b ∉ T.erase b := by simp
  rcases prob_7_3_finset_away_point_has_positive_distance (T.erase b) hbErase with
    ⟨ρR, hρR, hrightDist⟩
  refine ⟨min ρL ρR, lt_min hρL hρR, ?_, ?_⟩
  · intro x hxT
    have hxI := hT x hxT
    have hxne : x ≠ a := by
      intro hxa
      exact haT (by simpa [hxa] using hxT)
    have hdist := hleftDist x hxT
    have habs : |x - a| = x - a := abs_of_nonneg (sub_nonneg.mpr hxI.1)
    exact le_trans (min_le_left ρL ρR) (by simpa [habs] using hdist)
  · intro x hxT hxb
    have hxI := hT x hxT
    have hxErase : x ∈ T.erase b := by
      exact Finset.mem_erase.mpr ⟨hxb, hxT⟩
    have hdist := hrightDist x hxErase
    have habs : |x - b| = b - x := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hxI.2)
    exact le_trans (min_le_right ρL ρR) (by simpa [habs] using hdist)

theorem prob_7_3_finset_Icc_away_left_has_uniform_partition_radius
    {a b δ : ℝ} (T : Finset ℝ)
    (hδ : 0 < δ)
    (hT : ∀ x ∈ T, x ∈ Icc a b)
    (haT : a ∉ T) :
    ∃ ρ : ℝ,
      0 < ρ ∧ 4 * ρ < δ ∧
      (∀ x ∈ T, 2 * ρ ≤ x - a) ∧
      (∀ x ∈ T, x ≠ b → 2 * ρ ≤ b - x) ∧
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y → 4 * ρ ≤ |x - y|) := by
  rcases prob_7_3_finset_Icc_away_left_has_uniform_endpoint_margins
      (a := a) (b := b) T hT haT with
    ⟨ρE, hρE, hleftE, hrightE⟩
  let sepCap : ℝ :=
    if (T : Set ℝ).Nontrivial then (T : Set ℝ).infsep / 4 else 1
  have hsepCap_pos : 0 < sepCap := by
    dsimp [sepCap]
    by_cases hnon : (T : Set ℝ).Nontrivial
    · rw [if_pos hnon]
      have hinf_pos : 0 < (T : Set ℝ).infsep := by
        exact (Finset.infsep_pos_iff_nontrivial T).2 hnon
      linarith
    · rw [if_neg hnon]
      norm_num
  let ρ : ℝ := min (min (ρE / 2) (δ / 8)) sepCap
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (lt_min (by linarith) (by linarith)) hsepCap_pos
  refine ⟨ρ, hρ_pos, ?_, ?_, ?_, ?_⟩
  · have hρ_le_delta : ρ ≤ δ / 8 := by
      dsimp [ρ]
      exact le_trans (min_le_left (min (ρE / 2) (δ / 8)) sepCap)
        (min_le_right (ρE / 2) (δ / 8))
    linarith
  · intro x hxT
    have hρ_le_endpoint : ρ ≤ ρE / 2 := by
      dsimp [ρ]
      exact le_trans (min_le_left (min (ρE / 2) (δ / 8)) sepCap)
        (min_le_left (ρE / 2) (δ / 8))
    have h2ρ : 2 * ρ ≤ ρE := by linarith
    exact le_trans h2ρ (hleftE x hxT)
  · intro x hxT hxb
    have hρ_le_endpoint : ρ ≤ ρE / 2 := by
      dsimp [ρ]
      exact le_trans (min_le_left (min (ρE / 2) (δ / 8)) sepCap)
        (min_le_left (ρE / 2) (δ / 8))
    have h2ρ : 2 * ρ ≤ ρE := by linarith
    exact le_trans h2ρ (hrightE x hxT hxb)
  · intro x hxT y hyT hxy
    have hnon : (T : Set ℝ).Nontrivial := ⟨x, by simpa using hxT, y, by simpa using hyT, hxy⟩
    have hρ_le_sep : ρ ≤ (T : Set ℝ).infsep / 4 := by
      dsimp [ρ, sepCap]
      rw [if_pos hnon]
      exact min_le_right (min (ρE / 2) (δ / 8)) ((T : Set ℝ).infsep / 4)
    have h4ρ_le_inf : 4 * ρ ≤ (T : Set ℝ).infsep := by linarith
    have hinf_le_dist : (T : Set ℝ).infsep ≤ dist x y :=
      Set.infsep_le_dist_of_mem (by simpa using hxT) (by simpa using hyT) hxy
    exact le_trans h4ρ_le_inf (by simpa [Real.dist_eq] using hinf_le_dist)

theorem prob_7_3_left_protected_endpoint_strict_inside
    {a b ρ x : ℝ} (hρ : 0 < ρ)
    (_hxI : x ∈ Icc a b)
    (hleft : 2 * ρ ≤ x - a) :
    a < x - ρ ∧ x - ρ < x := by
  constructor <;> linarith

theorem prob_7_3_right_protected_endpoint_strict_inside
    {b ρ x : ℝ} (hρ : 0 < ρ)
    (hright : 2 * ρ ≤ b - x) :
    x < x + ρ ∧ x + ρ < b := by
  constructor <;> linarith

theorem prob_7_3_protected_endpoints_order_of_separated_centers
    {ρ x y : ℝ} (hρ : 0 < ρ)
    (hxy : x < y)
    (hsep : 4 * ρ ≤ |x - y|) :
    x + ρ < y - ρ := by
  have habs : |x - y| = y - x := by
    rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hxy))]
    ring
  have hgap : 4 * ρ ≤ y - x := by
    simpa [habs] using hsep
  linarith

noncomputable def prob_7_3_partitionOfEndpointFinset
    {a b : ℝ} (E : Finset ℝ)
    (ha : a ∈ E) (hb : b ∈ E)
    (hsub : ∀ x ∈ E, x ∈ Icc a b)
    (hab : a < b) :
    DarbouxRS.Partition a b := by
  let l : List ℝ := E.sort (fun x y : ℝ => x ≤ y)
  refine Thm11SourceRoute.partitionOfStrictEndpointList l ?_ ?_ ?_ ?_
  · refine Thm11SourceRoute.list_length_two_le_of_nodup_mem_ne
      (a := a) (b := b) ?_ ?_ ?_ ?_
    · dsimp [l]
      exact Finset.sort_nodup E (fun x y : ℝ => x ≤ y)
    · dsimp [l]
      rw [Finset.mem_sort]
      exact ha
    · dsimp [l]
      rw [Finset.mem_sort]
      exact hb
    · exact ne_of_lt hab
  · refine Thm11SourceRoute.sorted_list_getD_zero_eq_left ?_ ?_ ?_
    · dsimp [l]
      exact Finset.pairwise_sort E (fun x y : ℝ => x ≤ y)
    · dsimp [l]
      rw [Finset.mem_sort]
      exact ha
    · intro x hx
      dsimp [l] at hx
      rw [Finset.mem_sort] at hx
      exact hsub x hx
  · refine Thm11SourceRoute.sorted_list_getD_last_eq_right ?_ ?_ ?_
    · dsimp [l]
      exact Finset.pairwise_sort E (fun x y : ℝ => x ≤ y)
    · dsimp [l]
      rw [Finset.mem_sort]
      exact hb
    · intro x hx
      dsimp [l] at hx
      rw [Finset.mem_sort] at hx
      exact hsub x hx
  · intro i hi
    exact Thm11SourceRoute.sorted_nodup_adjacent_getD_lt
      (by
        dsimp [l]
        exact Finset.pairwise_sort E (fun x y : ℝ => x ≤ y))
      (by
        dsimp [l]
        exact Finset.sort_nodup E (fun x y : ℝ => x ≤ y))
      hi

theorem prob_7_3_partitionOfEndpointFinset_mesh_lt
    {a b δ : ℝ} (E : Finset ℝ)
    (ha : a ∈ E) (hb : b ∈ E)
    (hsub : ∀ x ∈ E, x ∈ Icc a b)
    (hab : a < b)
    (hgap : ∀ i : ℕ, i + 1 < (E.sort (fun x y : ℝ => x ≤ y)).length →
      (E.sort (fun x y : ℝ => x ≤ y)).getD (i + 1) b -
        (E.sort (fun x y : ℝ => x ≤ y)).getD i b < δ) :
    (prob_7_3_partitionOfEndpointFinset E ha hb hsub hab).mesh < δ := by
  unfold prob_7_3_partitionOfEndpointFinset
  unfold _root_.Partition.mesh
  rw [Finset.sup'_lt_iff]
  intro i _hi
  exact hgap i.val (by
    have hi' :
        i.val < (E.sort (fun x y : ℝ => x ≤ y)).length - 1 := i.isLt
    omega)

theorem prob_7_3_sorted_nodup_adjacent_of_no_mem_between
    {l : List ℝ} {fallback u v : ℝ}
    (hsorted : l.Pairwise (fun x y : ℝ => x ≤ y))
    (hnodup : l.Nodup)
    (hu : u ∈ l) (hv : v ∈ l)
    (huv : u < v)
    (hno : ∀ z : ℝ, z ∈ l → ¬ (u < z ∧ z < v)) :
    ∃ i : ℕ, i + 1 < l.length ∧
      l.getD i fallback = u ∧ l.getD (i + 1) fallback = v := by
  rcases List.mem_iff_getElem.1 hu with ⟨i, hi, hiu⟩
  rcases List.mem_iff_getElem.1 hv with ⟨j, hj, hjv⟩
  have hij_lt : i < j := by
    by_contra hnot
    have hji : j ≤ i := le_of_not_gt hnot
    by_cases hji_eq : j = i
    · subst j
      have huv_eq : u = v := hiu.symm.trans hjv
      exact (ne_of_lt huv) huv_eq
    · have hji_lt : j < i := lt_of_le_of_ne hji hji_eq
      have hv_le_u :
          v ≤ u := by
        have hle :=
          (List.pairwise_iff_getElem.mp hsorted) j i hj hi hji_lt
        simpa [hiu, hjv] using hle
      exact not_lt_of_ge hv_le_u huv
  have hsucc_eq : j = i + 1 := by
    by_contra hne
    have hsucc_lt : i + 1 < j := by omega
    have hsucc_len : i + 1 < l.length := Nat.lt_trans hsucc_lt hj
    let z : ℝ := l[i + 1]
    have hz_mem : z ∈ l := List.getElem_mem (l := l) (n := i + 1) hsucc_len
    have hu_le_z : u ≤ z := by
      have hle :=
        (List.pairwise_iff_getElem.mp hsorted) i (i + 1) hi hsucc_len
          (Nat.lt_succ_self i)
      simpa [hiu, z] using hle
    have hz_ne_u : z ≠ u := by
      intro hzu
      have hidx : i + 1 = i := by
        exact (List.Nodup.getElem_inj_iff (l := l) hnodup
          (i := i + 1) (hi := hsucc_len) (j := i) (hj := hi)).1
          (by simpa [z, hiu] using hzu)
      omega
    have hu_lt_z : u < z := lt_of_le_of_ne hu_le_z (Ne.symm hz_ne_u)
    have z_le_v : z ≤ v := by
      have hle :=
        (List.pairwise_iff_getElem.mp hsorted) (i + 1) j hsucc_len hj hsucc_lt
      simpa [z, hjv] using hle
    have hz_ne_v : z ≠ v := by
      intro hzv
      have hidx : i + 1 = j := by
        exact (List.Nodup.getElem_inj_iff (l := l) hnodup
          (i := i + 1) (hi := hsucc_len) (j := j) (hj := hj)).1
          (by simpa [z, hjv] using hzv)
      omega
    have hz_lt_v : z < v := lt_of_le_of_ne z_le_v hz_ne_v
    exact (hno z hz_mem) ⟨hu_lt_z, hz_lt_v⟩
  subst j
  refine ⟨i, ?_, ?_, ?_⟩
  · omega
  · rw [List.getD_eq_getElem l fallback hi]
    exact hiu
  · rw [List.getD_eq_getElem l fallback hj]
    exact hjv

noncomputable def prob_7_3_protectedEndpointSet
    (a b ρ : ℝ) (T : Finset ℝ) : Finset ℝ :=
  ({a, b} : Finset ℝ) ∪
    (T.image fun x : ℝ => x - ρ) ∪
    (T.image fun x : ℝ => if x = b then b else x + ρ)

theorem prob_7_3_left_mem_protectedEndpointSet
    {a b ρ : ℝ} (T : Finset ℝ) :
    a ∈ prob_7_3_protectedEndpointSet a b ρ T := by
  simp [prob_7_3_protectedEndpointSet]

theorem prob_7_3_right_mem_protectedEndpointSet
    {a b ρ : ℝ} (T : Finset ℝ) :
    b ∈ prob_7_3_protectedEndpointSet a b ρ T := by
  simp [prob_7_3_protectedEndpointSet]

theorem prob_7_3_center_left_endpoint_mem_protectedEndpointSet
    {a b ρ x : ℝ} {T : Finset ℝ} (hxT : x ∈ T) :
    x - ρ ∈ prob_7_3_protectedEndpointSet a b ρ T := by
  simp [prob_7_3_protectedEndpointSet, hxT]

theorem prob_7_3_center_right_endpoint_mem_protectedEndpointSet
    {a b ρ x : ℝ} {T : Finset ℝ} (hxT : x ∈ T) :
    (if x = b then b else x + ρ) ∈
      prob_7_3_protectedEndpointSet a b ρ T := by
  unfold prob_7_3_protectedEndpointSet
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image]
  exact Or.inr ⟨x, hxT, rfl⟩

theorem prob_7_3_protectedEndpointSet_subset_Icc
    {a b ρ : ℝ} (T : Finset ℝ)
    (hab : a < b)
    (hρ : 0 < ρ)
    (hT : ∀ x ∈ T, x ∈ Icc a b)
    (hleft : ∀ x ∈ T, 2 * ρ ≤ x - a)
    (hright : ∀ x ∈ T, x ≠ b → 2 * ρ ≤ b - x) :
    ∀ z ∈ prob_7_3_protectedEndpointSet a b ρ T, z ∈ Icc a b := by
  intro z hz
  simp only [prob_7_3_protectedEndpointSet, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_image] at hz
  rcases hz with ((rfl | rfl) | hzLeft) | hzRight
  · exact ⟨le_rfl, le_of_lt hab⟩
  · exact ⟨le_of_lt hab, le_rfl⟩
  · rcases hzLeft with ⟨x, hxT, rfl⟩
    have hxI := hT x hxT
    have hxleft := hleft x hxT
    refine ⟨?_, ?_⟩
    · linarith
    · exact le_trans (by linarith : x - ρ ≤ x) hxI.2
  · rcases hzRight with ⟨x, hxT, hzEq⟩
    by_cases hxb : x = b
    · have hz_b : z = b := by
        rw [← hzEq]
        simp [hxb]
      rw [hz_b]
      exact ⟨le_of_lt hab, le_rfl⟩
    · have hxI := hT x hxT
      have hxright := hright x hxT hxb
      have hz_eq : z = x + ρ := by
        rw [← hzEq]
        simp [hxb]
      rw [hz_eq]
      exact ⟨le_trans hxI.1 (by linarith : x ≤ x + ρ), by linarith⟩

theorem prob_7_3_finset_protected_intervals_ordered
    {a b ρ : ℝ} (T : Finset ℝ)
    (hρ : 0 < ρ)
    (hT : ∀ x ∈ T, x ∈ Icc a b)
    (hleft : ∀ x ∈ T, 2 * ρ ≤ x - a)
    (hright : ∀ x ∈ T, x ≠ b → 2 * ρ ≤ b - x)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 4 * ρ ≤ |x - y|) :
    (∀ x ∈ T, a < x - ρ ∧ x - ρ < x ∧
      (x = b ∨ x + ρ < b)) ∧
    (∀ x ∈ T, ∀ y ∈ T, x < y → x + ρ < y - ρ) := by
  constructor
  · intro x hxT
    rcases prob_7_3_left_protected_endpoint_strict_inside
        (a := a) (b := b) (ρ := ρ) (x := x)
        hρ (hT x hxT) (hleft x hxT) with
      ⟨hleftA, hleftX⟩
    refine ⟨hleftA, hleftX, ?_⟩
    by_cases hxb : x = b
    · exact Or.inl hxb
    · exact Or.inr
        (prob_7_3_right_protected_endpoint_strict_inside
          (b := b) (ρ := ρ) (x := x) hρ (hright x hxT hxb)).2
  · intro x hxT y hyT hxy_lt
    exact prob_7_3_protected_endpoints_order_of_separated_centers
      (ρ := ρ) (x := x) (y := y) hρ hxy_lt
      (hsep x hxT y hyT (ne_of_lt hxy_lt))

theorem prob_7_3_protectedEndpointSet_no_mem_between_center_endpoints
    {a b ρ x z : ℝ} {T : Finset ℝ}
    (hρ : 0 < ρ)
    (hT : ∀ y ∈ T, y ∈ Icc a b)
    (hleft : ∀ y ∈ T, 2 * ρ ≤ y - a)
    (hright : ∀ y ∈ T, y ≠ b → 2 * ρ ≤ b - y)
    (hsep : ∀ y ∈ T, ∀ w ∈ T, y ≠ w → 4 * ρ ≤ |y - w|)
    (hxT : x ∈ T)
    (hz : z ∈ prob_7_3_protectedEndpointSet a b ρ T) :
    ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ)) := by
  intro hbetween
  rcases hbetween with ⟨hxLz, hzR⟩
  have hord := prob_7_3_finset_protected_intervals_ordered
    (T := T) (a := a) (b := b) (ρ := ρ)
    hρ hT hleft hright hsep
  have hxOrder := hord.1 x hxT
  simp only [prob_7_3_protectedEndpointSet, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_image] at hz
  rcases hz with ((hzA | hzB) | hzLeft) | hzRight
  · have hz_a : z = a := by simpa [eq_comm] using hzA
    rw [hz_a] at hxLz
    linarith [hxOrder.1]
  · have hz_b : z = b := by simpa [eq_comm] using hzB
    rw [hz_b] at hzR
    rcases hxOrder with ⟨_, _, hxRight⟩
    rcases hxRight with hxb | hxRightLt
    · simp [hxb] at hzR
    · by_cases hxb : x = b
      · subst x
        linarith
      · have hzR' : b < x + ρ := by
          simpa [hxb] using hzR
        linarith
  · rcases hzLeft with ⟨y, hyT, rfl⟩
    by_cases hyx : y = x
    · subst y
      linarith
    · by_cases hy_lt_x : y < x
      · linarith
      · have hxy : x < y := lt_of_le_of_ne (le_of_not_gt hy_lt_x) (Ne.symm hyx)
        by_cases hxb : x = b
        · subst x
          have hy_le_b := (hT y hyT).2
          linarith
        · have hright_xy : x + ρ < y - ρ := hord.2 x hxT y hyT hxy
          simp [hxb] at hzR
          linarith
  · rcases hzRight with ⟨y, hyT, hzEq⟩
    by_cases hyx : y = x
    · subst y
      have hz_eq : z = (if x = b then b else x + ρ) := hzEq.symm
      rw [hz_eq] at hzR
      exact (lt_irrefl _) hzR
    · by_cases hy_lt_x : y < x
      · by_cases hyb : y = b
        · subst y
          have hx_le_b := (hT x hxT).2
          linarith
        · have hyRight_lt_xLeft : y + ρ < x - ρ := hord.2 y hyT x hxT hy_lt_x
          have hz_eq : z = y + ρ := by
            rw [← hzEq]
            simp [hyb]
          rw [hz_eq] at hxLz
          linarith
      · have hxy : x < y := lt_of_le_of_ne (le_of_not_gt hy_lt_x) (Ne.symm hyx)
        by_cases hxb : x = b
        · subst x
          have hy_le_b := (hT y hyT).2
          linarith
        · have hxRight_lt_yLeft : x + ρ < y - ρ := hord.2 x hxT y hyT hxy
          by_cases hyb : y = b
          · have hz_eq : z = b := by
              rw [← hzEq]
              simp [hyb]
            rw [hz_eq] at hzR
            simp [hxb] at hzR
            have hxRightLtB : x + ρ < b := by
              rcases hxOrder with ⟨_, _, hxRight⟩
              exact hxRight.resolve_left hxb
            linarith
          · have hz_eq : z = y + ρ := by
              rw [← hzEq]
              simp [hyb]
            rw [hz_eq] at hzR
            simp [hxb] at hzR
            linarith

theorem prob_7_3_protectedEndpointSet_adjacent_center_endpoints
    {a b ρ x : ℝ} {T : Finset ℝ}
    (hρ : 0 < ρ)
    (hT : ∀ y ∈ T, y ∈ Icc a b)
    (hleft : ∀ y ∈ T, 2 * ρ ≤ y - a)
    (hright : ∀ y ∈ T, y ≠ b → 2 * ρ ≤ b - y)
    (hsep : ∀ y ∈ T, ∀ w ∈ T, y ≠ w → 4 * ρ ≤ |y - w|)
    (hxT : x ∈ T) :
    ∃ i : ℕ,
      i + 1 < ((prob_7_3_protectedEndpointSet a b ρ T).sort
        (fun u v : ℝ => u ≤ v)).length ∧
      ((prob_7_3_protectedEndpointSet a b ρ T).sort
        (fun u v : ℝ => u ≤ v)).getD i b = x - ρ ∧
      ((prob_7_3_protectedEndpointSet a b ρ T).sort
        (fun u v : ℝ => u ≤ v)).getD (i + 1) b =
          (if x = b then b else x + ρ) := by
  let E : Finset ℝ := prob_7_3_protectedEndpointSet a b ρ T
  let l : List ℝ := E.sort (fun u v : ℝ => u ≤ v)
  have hleftMemE : x - ρ ∈ E :=
    prob_7_3_center_left_endpoint_mem_protectedEndpointSet (a := a) (b := b)
      (ρ := ρ) (x := x) hxT
  have hrightMemE : (if x = b then b else x + ρ) ∈ E :=
    prob_7_3_center_right_endpoint_mem_protectedEndpointSet (a := a) (b := b)
      (ρ := ρ) (x := x) hxT
  have hleftMemL : x - ρ ∈ l := by
    dsimp [l]
    rw [Finset.mem_sort]
    exact hleftMemE
  have hrightMemL : (if x = b then b else x + ρ) ∈ l := by
    dsimp [l]
    rw [Finset.mem_sort]
    exact hrightMemE
  have hltEndpoints : x - ρ < (if x = b then b else x + ρ) := by
    by_cases hxb : x = b
    · subst x
      simp [hρ]
    · simp [hxb]
      linarith
  have hno :
      ∀ z : ℝ, z ∈ l →
        ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ)) := by
    intro z hzL
    have hzE : z ∈ E := by
      dsimp [l] at hzL
      rw [Finset.mem_sort] at hzL
      exact hzL
    exact prob_7_3_protectedEndpointSet_no_mem_between_center_endpoints
      (a := a) (b := b) (ρ := ρ) (x := x) (z := z)
      hρ hT hleft hright hsep hxT hzE
  rcases prob_7_3_sorted_nodup_adjacent_of_no_mem_between
      (l := l) (fallback := b) (u := x - ρ)
      (v := if x = b then b else x + ρ)
      (by
        dsimp [l, E]
        exact Finset.pairwise_sort
          (prob_7_3_protectedEndpointSet a b ρ T) (fun u v : ℝ => u ≤ v))
      (by
        dsimp [l, E]
        exact Finset.sort_nodup
          (prob_7_3_protectedEndpointSet a b ρ T) (fun u v : ℝ => u ≤ v))
      hleftMemL hrightMemL hltEndpoints hno with
    ⟨i, hi, hleftEq, hrightEq⟩
  refine ⟨i, ?_, ?_, ?_⟩
  · simpa [l, E] using hi
  · simpa [l, E] using hleftEq
  · simpa [l, E] using hrightEq

theorem prob_7_3_protectedEndpointSet_partition_with_cell_margins_of_sorted_gaps
    {a b ρ δ : ℝ} (T : Finset ℝ)
    (hab : a < b)
    (hρ : 0 < ρ)
    (hT : ∀ x ∈ T, x ∈ Icc a b)
    (hleft : ∀ x ∈ T, 2 * ρ ≤ x - a)
    (hright : ∀ x ∈ T, x ≠ b → 2 * ρ ≤ b - x)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 4 * ρ ≤ |x - y|)
    (hgap : ∀ i : ℕ,
      i + 1 < ((prob_7_3_protectedEndpointSet a b ρ T).sort
        (fun u v : ℝ => u ≤ v)).length →
      ((prob_7_3_protectedEndpointSet a b ρ T).sort
        (fun u v : ℝ => u ≤ v)).getD (i + 1) b -
        ((prob_7_3_protectedEndpointSet a b ρ T).sort
          (fun u v : ℝ => u ≤ v)).getD i b < δ) :
    ∃ P : DarbouxRS.Partition a b,
      P.mesh < δ ∧
      ∃ idx : ℝ → ℕ,
        (∀ x ∈ T, idx x < P.n) ∧
        (∀ x ∈ T, ρ ≤ x - DarbouxRS.ptNat P (idx x)) ∧
        (∀ x ∈ T,
          ρ ≤ DarbouxRS.ptNat P (idx x + 1) - x ∨
            (x = b ∧ DarbouxRS.ptNat P (idx x + 1) = b)) := by
  let E : Finset ℝ := prob_7_3_protectedEndpointSet a b ρ T
  have haE : a ∈ E :=
    prob_7_3_left_mem_protectedEndpointSet (b := b) (ρ := ρ) T
  have hbE : b ∈ E :=
    prob_7_3_right_mem_protectedEndpointSet (a := a) (ρ := ρ) T
  have hsubE : ∀ z ∈ E, z ∈ Icc a b := by
    intro z hz
    exact prob_7_3_protectedEndpointSet_subset_Icc
      (T := T) (a := a) (b := b) (ρ := ρ)
      hab hρ hT hleft hright z hz
  let P : DarbouxRS.Partition a b :=
    prob_7_3_partitionOfEndpointFinset E haE hbE hsubE hab
  have hmesh : P.mesh < δ := by
    dsimp [P]
    refine prob_7_3_partitionOfEndpointFinset_mesh_lt
      (E := E) (a := a) (b := b) (δ := δ)
      haE hbE hsubE hab ?_
    intro i hi
    simpa [E] using hgap i (by simpa [E] using hi)
  have hadj :
      ∀ x : ℝ, x ∈ T →
        ∃ i : ℕ,
          i + 1 < (E.sort (fun u v : ℝ => u ≤ v)).length ∧
          (E.sort (fun u v : ℝ => u ≤ v)).getD i b = x - ρ ∧
          (E.sort (fun u v : ℝ => u ≤ v)).getD (i + 1) b =
            (if x = b then b else x + ρ) := by
    intro x hxT
    simpa [E] using
      prob_7_3_protectedEndpointSet_adjacent_center_endpoints
        (a := a) (b := b) (ρ := ρ) (x := x) (T := T)
        hρ hT hleft hright hsep hxT
  let idx : ℝ → ℕ := fun x =>
    if hx : x ∈ T then Classical.choose (hadj x hx) else 0
  refine ⟨P, hmesh, idx, ?_, ?_, ?_⟩
  · intro x hxT
    have hspec := Classical.choose_spec (hadj x hxT)
    dsimp [idx]
    rw [dif_pos hxT]
    have hi : Classical.choose (hadj x hxT) + 1 <
        (E.sort (fun u v : ℝ => u ≤ v)).length := hspec.1
    dsimp [P, prob_7_3_partitionOfEndpointFinset]
    change Classical.choose (hadj x hxT) <
      (E.sort (fun u v : ℝ => u ≤ v)).length - 1
    omega
  · intro x hxT
    have hspec := Classical.choose_spec (hadj x hxT)
    dsimp [idx]
    rw [dif_pos hxT]
    have hleftEq :
        DarbouxRS.ptNat P (Classical.choose (hadj x hxT)) = x - ρ := by
      have hle : Classical.choose (hadj x hxT) ≤ P.n := by
        dsimp [P, prob_7_3_partitionOfEndpointFinset,
          Thm11SourceRoute.partitionOfStrictEndpointList]
        omega
      rw [DarbouxRS.ptNat, dif_pos hle]
      dsimp [P, prob_7_3_partitionOfEndpointFinset]
      exact hspec.2.1
    rw [hleftEq]
    linarith
  · intro x hxT
    have hspec := Classical.choose_spec (hadj x hxT)
    dsimp [idx]
    rw [dif_pos hxT]
    have hrightEq :
        DarbouxRS.ptNat P (Classical.choose (hadj x hxT) + 1) =
          (if x = b then b else x + ρ) := by
      have hle : Classical.choose (hadj x hxT) + 1 ≤ P.n := by
        dsimp [P, prob_7_3_partitionOfEndpointFinset,
          Thm11SourceRoute.partitionOfStrictEndpointList]
        omega
      rw [DarbouxRS.ptNat, dif_pos hle]
      dsimp [P, prob_7_3_partitionOfEndpointFinset]
      exact hspec.2.2
    by_cases hxb : x = b
    · right
      rw [hrightEq]
      simp [hxb]
    · left
      rw [hrightEq]
      simp [hxb]

theorem prob_7_3_exists_endpointFinset_for_interval_mesh
    {u v δ : ℝ} (huv : u < v) (hδ : 0 < δ) :
    ∃ E : Finset ℝ,
      u ∈ E ∧
      v ∈ E ∧
      (∀ z ∈ E, z ∈ Icc u v) ∧
      (∀ i : ℕ, i + 1 < (E.sort (fun x y : ℝ => x ≤ y)).length →
        (E.sort (fun x y : ℝ => x ≤ y)).getD (i + 1) v -
          (E.sort (fun x y : ℝ => x ≤ y)).getD i v < δ) := by
  rcases DarbouxRS.exists_partition_mesh_lt huv hδ with ⟨P, hPmesh⟩
  let E : Finset ℝ := Thm11SourceRoute.partitionPointSet P
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · exact Thm11SourceRoute.partitionPointSet_left_mem P
  · exact Thm11SourceRoute.partitionPointSet_right_mem P
  · intro z hz
    exact Thm11SourceRoute.partitionPointSet_subset_Icc P hz
  · intro i hi
    have hgap :=
      Thm11SourceRoute.commonRefinementPointList_adjacent_length_lt_delta
        (P := P) (Q := P) hPmesh hPmesh
        (by simpa [E, Thm11SourceRoute.commonRefinementPointList,
          Thm11SourceRoute.commonRefinementPointSet] using hi)
    simpa [E, Thm11SourceRoute.commonRefinementPointList,
      Thm11SourceRoute.commonRefinementPointSet] using hgap

theorem prob_7_3_endpointFinset_clean_cells_to_partition_with_cell_margins
    {a b ρ δ : ℝ} (T E : Finset ℝ)
    (hab : a < b)
    (hρ : 0 < ρ)
    (hProtected : prob_7_3_protectedEndpointSet a b ρ T ⊆ E)
    (haE : a ∈ E)
    (hbE : b ∈ E)
    (hEsub : ∀ z ∈ E, z ∈ Icc a b)
    (hgap : ∀ i : ℕ, i + 1 < (E.sort (fun u v : ℝ => u ≤ v)).length →
      (E.sort (fun u v : ℝ => u ≤ v)).getD (i + 1) b -
        (E.sort (fun u v : ℝ => u ≤ v)).getD i b < δ)
    (hclean : ∀ x ∈ T, ∀ z ∈ E,
      ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ))) :
    ∃ P : DarbouxRS.Partition a b,
      P.mesh < δ ∧
      ∃ idx : ℝ → ℕ,
        (∀ x ∈ T, idx x < P.n) ∧
        (∀ x ∈ T, ρ ≤ x - DarbouxRS.ptNat P (idx x)) ∧
        (∀ x ∈ T,
          ρ ≤ DarbouxRS.ptNat P (idx x + 1) - x ∨
            (x = b ∧ DarbouxRS.ptNat P (idx x + 1) = b)) := by
  let P : DarbouxRS.Partition a b :=
    prob_7_3_partitionOfEndpointFinset E haE hbE hEsub hab
  have hmesh : P.mesh < δ := by
    dsimp [P]
    exact prob_7_3_partitionOfEndpointFinset_mesh_lt
      (E := E) (a := a) (b := b) (δ := δ)
      haE hbE hEsub hab hgap
  have hadj :
      ∀ x : ℝ, x ∈ T →
        ∃ i : ℕ,
          i + 1 < (E.sort (fun u v : ℝ => u ≤ v)).length ∧
          (E.sort (fun u v : ℝ => u ≤ v)).getD i b = x - ρ ∧
          (E.sort (fun u v : ℝ => u ≤ v)).getD (i + 1) b =
            (if x = b then b else x + ρ) := by
    intro x hxT
    have hleftMemE : x - ρ ∈ E :=
      hProtected
        (prob_7_3_center_left_endpoint_mem_protectedEndpointSet
          (a := a) (b := b) (ρ := ρ) (x := x) hxT)
    have hrightMemE : (if x = b then b else x + ρ) ∈ E :=
      hProtected
        (prob_7_3_center_right_endpoint_mem_protectedEndpointSet
          (a := a) (b := b) (ρ := ρ) (x := x) hxT)
    have hleftMemL : x - ρ ∈ E.sort (fun u v : ℝ => u ≤ v) := by
      rw [Finset.mem_sort]
      exact hleftMemE
    have hrightMemL :
        (if x = b then b else x + ρ) ∈ E.sort (fun u v : ℝ => u ≤ v) := by
      rw [Finset.mem_sort]
      exact hrightMemE
    have hltEndpoints : x - ρ < (if x = b then b else x + ρ) := by
      by_cases hxb : x = b
      · subst x
        simp [hρ]
      · simp [hxb]
        linarith
    have hno :
        ∀ z : ℝ, z ∈ E.sort (fun u v : ℝ => u ≤ v) →
          ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ)) := by
      intro z hzL
      have hzE : z ∈ E := by
        rw [Finset.mem_sort] at hzL
        exact hzL
      exact hclean x hxT z hzE
    exact prob_7_3_sorted_nodup_adjacent_of_no_mem_between
      (l := E.sort (fun u v : ℝ => u ≤ v)) (fallback := b)
      (u := x - ρ) (v := if x = b then b else x + ρ)
      (Finset.pairwise_sort E (fun u v : ℝ => u ≤ v))
      (Finset.sort_nodup E (fun u v : ℝ => u ≤ v))
      hleftMemL hrightMemL hltEndpoints hno
  let idx : ℝ → ℕ := fun x =>
    if hx : x ∈ T then Classical.choose (hadj x hx) else 0
  refine ⟨P, hmesh, idx, ?_, ?_, ?_⟩
  · intro x hxT
    have hspec := Classical.choose_spec (hadj x hxT)
    dsimp [idx]
    rw [dif_pos hxT]
    have hi : Classical.choose (hadj x hxT) + 1 <
        (E.sort (fun u v : ℝ => u ≤ v)).length := hspec.1
    dsimp [P, prob_7_3_partitionOfEndpointFinset]
    change Classical.choose (hadj x hxT) <
      (E.sort (fun u v : ℝ => u ≤ v)).length - 1
    omega
  · intro x hxT
    have hspec := Classical.choose_spec (hadj x hxT)
    dsimp [idx]
    rw [dif_pos hxT]
    have hleftEq :
        DarbouxRS.ptNat P (Classical.choose (hadj x hxT)) = x - ρ := by
      have hle : Classical.choose (hadj x hxT) ≤ P.n := by
        dsimp [P, prob_7_3_partitionOfEndpointFinset,
          Thm11SourceRoute.partitionOfStrictEndpointList]
        omega
      rw [DarbouxRS.ptNat, dif_pos hle]
      dsimp [P, prob_7_3_partitionOfEndpointFinset]
      exact hspec.2.1
    rw [hleftEq]
    linarith
  · intro x hxT
    have hspec := Classical.choose_spec (hadj x hxT)
    dsimp [idx]
    rw [dif_pos hxT]
    have hrightEq :
        DarbouxRS.ptNat P (Classical.choose (hadj x hxT) + 1) =
          (if x = b then b else x + ρ) := by
      have hle : Classical.choose (hadj x hxT) + 1 ≤ P.n := by
        dsimp [P, prob_7_3_partitionOfEndpointFinset,
          Thm11SourceRoute.partitionOfStrictEndpointList]
        omega
      rw [DarbouxRS.ptNat, dif_pos hle]
      dsimp [P, prob_7_3_partitionOfEndpointFinset]
      exact hspec.2.2
    by_cases hxb : x = b
    · right
      rw [hrightEq]
      simp [hxb]
    · left
      rw [hrightEq]
      simp [hxb]

theorem prob_7_3_isCompact_cleanEndpointComplement
    {a b ρ : ℝ} (T : Finset ℝ) :
    IsCompact
      (Icc a b ∩
        ⋂ x ∈ T,
          {z : ℝ | ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ))}) := by
  have hclosedClean :
      IsClosed
        (⋂ x ∈ T,
          {z : ℝ | ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ))}) := by
    refine isClosed_iInter ?_
    intro x
    refine isClosed_iInter ?_
    intro _hxT
    have hopen :
        IsOpen (Ioo (x - ρ) (if x = b then b else x + ρ) : Set ℝ) :=
      isOpen_Ioo
    simpa [Ioo, Set.compl_setOf] using hopen.isClosed_compl
  exact isCompact_Icc.inter_right hclosedClean

theorem prob_7_3_exists_endpointFinset_refining_protectedEndpointSet_with_mesh_and_clean_cells
    {a b ρ δ : ℝ} (T : Finset ℝ)
    (hab : a < b)
    (hρ : 0 < ρ)
    (hδ : 0 < δ)
    (hrho_delta : 4 * ρ < δ)
    (hT : ∀ x ∈ T, x ∈ Icc a b)
    (hleft : ∀ x ∈ T, 2 * ρ ≤ x - a)
    (hright : ∀ x ∈ T, x ≠ b → 2 * ρ ≤ b - x)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 4 * ρ ≤ |x - y|) :
    ∃ E : Finset ℝ,
      prob_7_3_protectedEndpointSet a b ρ T ⊆ E ∧
      a ∈ E ∧
      b ∈ E ∧
      (∀ z ∈ E, z ∈ Icc a b) ∧
      (∀ i : ℕ, i + 1 < (E.sort (fun x y : ℝ => x ≤ y)).length →
        (E.sort (fun x y : ℝ => x ≤ y)).getD (i + 1) b -
          (E.sort (fun x y : ℝ => x ≤ y)).getD i b < δ) ∧
      (∀ x ∈ T, ∀ z ∈ E,
        ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ))) := by
  classical
  let K : Set ℝ :=
    Icc a b ∩
      ⋂ x ∈ T,
        {z : ℝ | ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ))}
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact prob_7_3_isCompact_cleanEndpointComplement
      (a := a) (b := b) (ρ := ρ) T
  have hδ4 : 0 < δ / 4 := by
    exact div_pos hδ (by norm_num)
  rcases prob_7_3_compact_finite_uniform_ball_subcover
      (K := K) (ρ := δ / 4) hKcompact hδ4 with
    ⟨N, hNsubK, hNcover⟩
  let E : Finset ℝ := prob_7_3_protectedEndpointSet a b ρ T ∪ N
  have hProtected : prob_7_3_protectedEndpointSet a b ρ T ⊆ E := by
    intro z hz
    exact Finset.mem_union.mpr (Or.inl hz)
  have haE : a ∈ E := by
    exact hProtected (prob_7_3_left_mem_protectedEndpointSet (b := b) (ρ := ρ) T)
  have hbE : b ∈ E := by
    exact hProtected (prob_7_3_right_mem_protectedEndpointSet (a := a) (ρ := ρ) T)
  have hEsub : ∀ z ∈ E, z ∈ Icc a b := by
    intro z hzE
    rw [Finset.mem_union] at hzE
    rcases hzE with hzP | hzN
    · exact prob_7_3_protectedEndpointSet_subset_Icc
        (T := T) (a := a) (b := b) (ρ := ρ)
        hab hρ hT hleft hright z hzP
    · exact (hNsubK z hzN).1
  have hcleanE :
      ∀ x ∈ T, ∀ z ∈ E,
        ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ)) := by
    intro x hxT z hzE
    rw [Finset.mem_union] at hzE
    rcases hzE with hzP | hzN
    · exact prob_7_3_protectedEndpointSet_no_mem_between_center_endpoints
        (a := a) (b := b) (ρ := ρ) (x := x) (z := z) (T := T)
        hρ hT hleft hright hsep hxT hzP
    · have hzK := hNsubK z hzN
      have hzCleanAll : z ∈
          (⋂ x ∈ T,
            {z : ℝ | ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ))}) := by
        exact hzK.2
      have hzCleanX :
          z ∈ {z : ℝ | ¬ (x - ρ < z ∧ z < (if x = b then b else x + ρ))} := by
        exact mem_iInter.mp (mem_iInter.mp hzCleanAll x) hxT
      exact hzCleanX
  have hgap :
      ∀ i : ℕ, i + 1 < (E.sort (fun x y : ℝ => x ≤ y)).length →
        (E.sort (fun x y : ℝ => x ≤ y)).getD (i + 1) b -
          (E.sort (fun x y : ℝ => x ≤ y)).getD i b < δ := by
    intro i hi
    let l : List ℝ := E.sort (fun x y : ℝ => x ≤ y)
    let u : ℝ := l.getD i b
    let v : ℝ := l.getD (i + 1) b
    have hi_l : i + 1 < l.length := by
      simpa [l] using hi
    have hi0_l : i < l.length := Nat.lt_trans (Nat.lt_succ_self i) hi_l
    have hsorted : l.Pairwise (fun x y : ℝ => x ≤ y) := by
      dsimp [l]
      exact Finset.pairwise_sort E (fun x y : ℝ => x ≤ y)
    have hnodup : l.Nodup := by
      dsimp [l]
      exact Finset.sort_nodup E (fun x y : ℝ => x ≤ y)
    have huv : u < v := by
      dsimp [u, v]
      exact Thm11SourceRoute.sorted_nodup_adjacent_getD_lt
        hsorted hnodup hi_l
    have huL : u ∈ l := by
      dsimp [u]
      exact Thm11SourceRoute.list_getD_mem_of_lt (l := l) (fallback := b) hi0_l
    have hvL : v ∈ l := by
      dsimp [v]
      exact Thm11SourceRoute.list_getD_mem_of_lt (l := l) (fallback := b) hi_l
    have huE : u ∈ E := by
      dsimp [l] at huL
      rw [Finset.mem_sort] at huL
      exact huL
    have hvE : v ∈ E := by
      dsimp [l] at hvL
      rw [Finset.mem_sort] at hvL
      exact hvL
    have huI : u ∈ Icc a b := hEsub u huE
    have hvI : v ∈ Icc a b := hEsub v hvE
    have hnoBetweenE : ∀ z ∈ E, ¬ (u < z ∧ z < v) := by
      intro z hzE
      have hzL : z ∈ l := by
        dsimp [l]
        rw [Finset.mem_sort]
        exact hzE
      exact Thm11SourceRoute.sorted_nodup_adjacent_no_mem_between
        (l := l) (fallback := b) hsorted hi_l hzL
    by_contra hnot
    have hδle : δ ≤ v - u := le_of_not_gt hnot
    let m : ℝ := (u + v) / 2
    have hum : u < m := by
      dsimp [m]
      linarith
    have hmv : m < v := by
      dsimp [m]
      linarith
    have hmI : m ∈ Icc a b := by
      refine ⟨?_, ?_⟩
      · linarith [huI.1, le_of_lt hum]
      · linarith [hvI.2, le_of_lt hmv]
    by_cases hmClean :
        ∀ x ∈ T, ¬ (x - ρ < m ∧ m < (if x = b then b else x + ρ))
    · have hmK : m ∈ K := by
        refine ⟨hmI, ?_⟩
        rw [mem_iInter]
        intro x
        rw [mem_iInter]
        intro hxT
        exact hmClean x hxT
      have hmCover := hNcover hmK
      rw [mem_iUnion] at hmCover
      rcases hmCover with ⟨y, hmCover⟩
      rw [mem_iUnion] at hmCover
      rcases hmCover with ⟨hyN, hymBall⟩
      have hyClose : |y - m| < δ / 4 := by
        simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hymBall
      have hgap_pos : 0 < v - u := sub_pos.mpr huv
      have hquarter_lt_half : δ / 4 < (v - u) / 2 := by
        nlinarith
      have hyLeft : m - δ / 4 < y := by
        have h := (abs_lt.mp hyClose).1
        linarith
      have hyRight : y < m + δ / 4 := by
        have h := (abs_lt.mp hyClose).2
        linarith
      have huEq : u = m - (v - u) / 2 := by
        dsimp [m]
        ring
      have hvEq : v = m + (v - u) / 2 := by
        dsimp [m]
        ring
      have huy : u < y := by
        rw [huEq]
        linarith
      have hyv : y < v := by
        rw [hvEq]
        linarith
      have hyE : y ∈ E := Finset.mem_union.mpr (Or.inr hyN)
      exact (hnoBetweenE y hyE) ⟨huy, hyv⟩
    · push_neg at hmClean
      rcases hmClean with ⟨x, hxT, hxm⟩
      let L : ℝ := x - ρ
      let R : ℝ := if x = b then b else x + ρ
      have hLmemE : L ∈ E := by
        exact hProtected (by
          simpa [L] using
            (prob_7_3_center_left_endpoint_mem_protectedEndpointSet
              (a := a) (b := b) (ρ := ρ) (x := x) hxT))
      have hRmemE : R ∈ E := by
        exact hProtected (by
          simpa [R] using
            (prob_7_3_center_right_endpoint_mem_protectedEndpointSet
              (a := a) (b := b) (ρ := ρ) (x := x) hxT))
      have hLm : L < m := by
        simpa [L, R] using hxm.1
      have hmR : m < R := by
        simpa [L, R] using hxm.2
      have huClean := hcleanE x hxT u huE
      have hvClean := hcleanE x hxT v hvE
      have hu_le_L : u ≤ L := by
        by_contra hnot_le
        have hL_lt_u : L < u := lt_of_not_ge hnot_le
        have hu_lt_R : u < R := lt_trans hum hmR
        exact huClean ⟨hL_lt_u, hu_lt_R⟩
      have hR_le_v : R ≤ v := by
        by_contra hnot_le
        have hv_lt_R : v < R := lt_of_not_ge hnot_le
        have hL_lt_v : L < v := lt_trans hLm hmv
        exact hvClean ⟨hL_lt_v, hv_lt_R⟩
      by_cases hu_lt_L : u < L
      · have hL_lt_v : L < v := lt_trans hLm hmv
        exact (hnoBetweenE L hLmemE) ⟨hu_lt_L, hL_lt_v⟩
      have hL_eq_u : L = u := le_antisymm (le_of_not_gt hu_lt_L) hu_le_L
      by_cases hR_lt_v : R < v
      · have hu_lt_R : u < R := by
          rw [← hL_eq_u]
          exact lt_trans hLm hmR
        exact (hnoBetweenE R hRmemE) ⟨hu_lt_R, hR_lt_v⟩
      have hR_eq_v : R = v := le_antisymm hR_le_v (le_of_not_gt hR_lt_v)
      have hgapEq : v - u = R - L := by
        rw [← hR_eq_v, ← hL_eq_u]
      have hRL_lt_delta : R - L < δ := by
        by_cases hxb : x = b
        · dsimp [R, L]
          simp [hxb]
          nlinarith
        · dsimp [R, L]
          simp [hxb]
          nlinarith
      have hvu_lt_delta : v - u < δ := by
        simpa [hgapEq] using hRL_lt_delta
      exact hnot hvu_lt_delta
  exact ⟨E, hProtected, haE, hbE, hEsub, hgap, hcleanE⟩
