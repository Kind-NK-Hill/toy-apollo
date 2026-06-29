import ToyApollo.Output.prob_7_3_partition_support

open MeasureTheory Set Filter

noncomputable section

theorem prob_7_3_finite_centers_to_partition_with_cell_margins
    {a b δ : ℝ} (T : Finset ℝ)
    (hab : a < b)
    (hδ : 0 < δ)
    (hT : ∀ x ∈ T, x ∈ Icc a b)
    (haT : a ∉ T) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∃ P : DarbouxRS.Partition a b,
        P.mesh < δ ∧
        ∃ idx : ℝ → ℕ,
          (∀ x ∈ T, idx x < P.n) ∧
          (∀ x ∈ T, ρ ≤ x - P.pts (idx x)) ∧
          (∀ x ∈ T,
            ρ ≤ P.pts (idx x + 1) - x ∨
              (x = b ∧ P.pts (idx x + 1) = b)) := by
  rcases prob_7_3_finset_Icc_away_left_has_uniform_partition_radius
      (T := T) (a := a) (b := b) (δ := δ) hδ hT haT with
    ⟨ρ, hρ, hρδ, hleft, hright, hsep⟩
  rcases
      prob_7_3_exists_endpointFinset_refining_protectedEndpointSet_with_mesh_and_clean_cells
        (T := T) (a := a) (b := b) (ρ := ρ) (δ := δ)
        hab hρ hδ hρδ hT hleft hright hsep with
    ⟨E, hProtected, haE, hbE, hEsub, hgap, hclean⟩
  rcases prob_7_3_endpointFinset_clean_cells_to_partition_with_cell_margins
      (T := T) (E := E) (a := a) (b := b) (ρ := ρ) (δ := δ)
      hab hρ hProtected haE hbE hEsub hgap hclean with
    ⟨P, hmesh, idx, hidx, hleftMargin, hrightMargin⟩
  exact ⟨ρ, hρ, P, hmesh, idx, hidx, hleftMargin, hrightMargin⟩

theorem prob_7_3_compact_largeOscillation_finite_uniform_ball_subcover
    {a b ρ : ℝ} {f : ℝ → ℝ} {K : Set ℝ} (n : ℕ)
    (hKcompact : IsCompact K)
    (hKsub : K ⊆ prob_7_3_largeOscillationSet f a b n)
    (hρ : 0 < ρ) :
    ∃ S : Finset ℝ,
      (∀ x ∈ S, x ∈ K) ∧
      (∀ x ∈ S, x ∈ prob_7_3_largeOscillationSet f a b n) ∧
      K ⊆ ⋃ x ∈ S, Metric.ball x ρ := by
  rcases prob_7_3_compact_finite_uniform_ball_subcover
      (K := K) hKcompact hρ with
    ⟨S, hSK, hcover⟩
  exact ⟨S, hSK, fun x hxS => hKsub (hSK x hxS), hcover⟩

theorem prob_7_3_finite_centers_to_protected_cell_cover
    {a b ρ : ℝ} {f : ℝ → ℝ} {K : Set ℝ} (n : ℕ)
    (P : DarbouxRS.Partition a b) (T : Finset ℝ) (idx : ℝ → ℕ)
    (hρ : 0 < ρ)
    (hKcover : K ⊆ ⋃ x ∈ T, Metric.ball x ρ)
    (hcenter : ∀ x ∈ T, x ∈ prob_7_3_largeOscillationSet f a b n)
    (hidx : ∀ x ∈ T, idx x < P.n)
    (hballIoc : ∀ x ∈ T, Metric.ball x ρ ⊆
      Ioc (P.pts (idx x)) (P.pts (idx x + 1)))
    (hprotected : ∀ x ∈ T, ∀ y : ℝ, y ∈ Icc a b → |y - x| < ρ →
      y ∈ DarbouxRS.subinterval P (idx x)) :
    ∃ S : Finset ℕ,
      (∀ i ∈ S, i < P.n) ∧
      K ⊆ ⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)) ∧
      (∀ i ∈ S, ∃ x r : ℝ,
        x ∈ prob_7_3_largeOscillationSet f a b n ∧
          0 < r ∧
          ∀ y : ℝ, y ∈ Icc a b → |y - x| < r →
            y ∈ DarbouxRS.subinterval P i) := by
  classical
  let S : Finset ℕ := T.image idx
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i hiS
    rcases Finset.mem_image.mp hiS with ⟨x, hxT, rfl⟩
    exact hidx x hxT
  · intro z hzK
    have hzCover := hKcover hzK
    rw [mem_iUnion] at hzCover
    rcases hzCover with ⟨x, hzCover⟩
    rw [mem_iUnion] at hzCover
    rcases hzCover with ⟨hxT, hzBall⟩
    rw [mem_iUnion]
    refine ⟨idx x, ?_⟩
    rw [mem_iUnion]
    refine ⟨Finset.mem_image.mpr ⟨x, hxT, rfl⟩, ?_⟩
    exact hballIoc x hxT hzBall
  · intro i hiS
    rcases Finset.mem_image.mp hiS with ⟨x, hxT, hidx_eq⟩
    refine ⟨x, ρ, hcenter x hxT, hρ, ?_⟩
    intro y hyI hydist
    simpa [hidx_eq] using hprotected x hxT y hyI hydist

theorem prob_7_3_finite_centers_to_protected_cell_cover_Icc
    {a b ρ : ℝ} {f : ℝ → ℝ} {K : Set ℝ} (n : ℕ)
    (P : DarbouxRS.Partition a b) (T : Finset ℝ) (idx : ℝ → ℕ)
    (hρ : 0 < ρ)
    (hKIcc : K ⊆ Icc a b)
    (hKcover : K ⊆ ⋃ x ∈ T, Metric.ball x ρ)
    (hcenter : ∀ x ∈ T, x ∈ prob_7_3_largeOscillationSet f a b n)
    (hidx : ∀ x ∈ T, idx x < P.n)
    (hballIoc : ∀ x ∈ T, ∀ y : ℝ, y ∈ Icc a b → y ∈ Metric.ball x ρ →
      y ∈ Ioc (P.pts (idx x)) (P.pts (idx x + 1)))
    (hprotected : ∀ x ∈ T, ∀ y : ℝ, y ∈ Icc a b → |y - x| < ρ →
      y ∈ DarbouxRS.subinterval P (idx x)) :
    ∃ S : Finset ℕ,
      (∀ i ∈ S, i < P.n) ∧
      K ⊆ ⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)) ∧
      (∀ i ∈ S, ∃ x r : ℝ,
        x ∈ prob_7_3_largeOscillationSet f a b n ∧
          0 < r ∧
          ∀ y : ℝ, y ∈ Icc a b → |y - x| < r →
            y ∈ DarbouxRS.subinterval P i) := by
  classical
  let S : Finset ℕ := T.image idx
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i hiS
    rcases Finset.mem_image.mp hiS with ⟨x, hxT, rfl⟩
    exact hidx x hxT
  · intro z hzK
    have hzCover := hKcover hzK
    rw [mem_iUnion] at hzCover
    rcases hzCover with ⟨x, hzCover⟩
    rw [mem_iUnion] at hzCover
    rcases hzCover with ⟨hxT, hzBall⟩
    rw [mem_iUnion]
    refine ⟨idx x, ?_⟩
    rw [mem_iUnion]
    refine ⟨Finset.mem_image.mpr ⟨x, hxT, rfl⟩, ?_⟩
    exact hballIoc x hxT z (hKIcc hzK) hzBall
  · intro i hiS
    rcases Finset.mem_image.mp hiS with ⟨x, hxT, hidx_eq⟩
    refine ⟨x, ρ, hcenter x hxT, hρ, ?_⟩
    intro y hyI hydist
    simpa [hidx_eq] using hprotected x hxT y hyI hydist

theorem prob_7_3_cell_margins_give_relative_ball_Ioc_and_subinterval
    {a b ρ x : ℝ} (P : DarbouxRS.Partition a b) {i : ℕ}
    (hleft : ρ ≤ x - P.pts i)
    (hright : ρ ≤ P.pts (i + 1) - x ∨ (x = b ∧ P.pts (i + 1) = b)) :
    (∀ y : ℝ, y ∈ Icc a b → y ∈ Metric.ball x ρ →
      y ∈ Ioc (P.pts i) (P.pts (i + 1))) ∧
    (∀ y : ℝ, y ∈ Icc a b → |y - x| < ρ →
      y ∈ DarbouxRS.subinterval P i) := by
  have hIoc : ∀ y : ℝ, y ∈ Icc a b → y ∈ Metric.ball x ρ →
      y ∈ Ioc (P.pts i) (P.pts (i + 1)) := by
    intro y hyI hyBall
    have hydist : |y - x| < ρ := by
      simpa [Metric.mem_ball, Real.dist_eq] using hyBall
    have hlt_left : P.pts i < y := by
      have hneg : x - y < ρ := by
        exact lt_of_le_of_lt (le_abs_self (x - y)) (by simpa [abs_sub_comm] using hydist)
      linarith
    have hle_right : y ≤ P.pts (i + 1) := by
      rcases hright with hright' | hend
      · have hpos : y - x < ρ := by
          exact lt_of_le_of_lt (le_abs_self (y - x)) hydist
        linarith
      · rcases hend with ⟨rfl, hPend⟩
        simpa [hPend] using hyI.2
    exact ⟨hlt_left, hle_right⟩
  refine ⟨hIoc, ?_⟩
  intro y hyI hydist
  have hyIoc :
      y ∈ Ioc (P.pts i) (P.pts (i + 1)) := by
    exact hIoc y hyI (by
      simpa [Metric.mem_ball, Real.dist_eq] using hydist)
  exact ⟨le_of_lt hyIoc.1, hyIoc.2⟩

theorem prob_7_3_finite_centers_with_cell_margins_to_protected_cell_cover
    {a b ρ : ℝ} {f : ℝ → ℝ} {K : Set ℝ} (n : ℕ)
    (P : DarbouxRS.Partition a b) (T : Finset ℝ) (idx : ℝ → ℕ)
    (hρ : 0 < ρ)
    (hKIcc : K ⊆ Icc a b)
    (hKcover : K ⊆ ⋃ x ∈ T, Metric.ball x ρ)
    (hcenter : ∀ x ∈ T, x ∈ prob_7_3_largeOscillationSet f a b n)
    (hidx : ∀ x ∈ T, idx x < P.n)
    (hleft : ∀ x ∈ T, ρ ≤ x - P.pts (idx x))
    (hright : ∀ x ∈ T,
      ρ ≤ P.pts (idx x + 1) - x ∨ (x = b ∧ P.pts (idx x + 1) = b)) :
    ∃ S : Finset ℕ,
      (∀ i ∈ S, i < P.n) ∧
      K ⊆ ⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)) ∧
      (∀ i ∈ S, ∃ x r : ℝ,
        x ∈ prob_7_3_largeOscillationSet f a b n ∧
          0 < r ∧
          ∀ y : ℝ, y ∈ Icc a b → |y - x| < r →
            y ∈ DarbouxRS.subinterval P i) := by
  refine prob_7_3_finite_centers_to_protected_cell_cover_Icc
    (n := n) (P := P) (T := T) (idx := idx) hρ hKIcc hKcover hcenter hidx ?_ ?_
  · intro x hxT y hyI hyBall
    exact (prob_7_3_cell_margins_give_relative_ball_Ioc_and_subinterval
      (P := P) (i := idx x) (hleft x hxT) (hright x hxT)).1 y hyI hyBall
  · intro x hxT y hyI hydist
    exact (prob_7_3_cell_margins_give_relative_ball_Ioc_and_subinterval
      (P := P) (i := idx x) (hleft x hxT) (hright x hxT)).2 y hyI hydist

theorem prob_7_3_cell_oscillation_lower_bound_of_two_points
    {a b eta : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ} (hi : i < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    {y z : ℝ}
    (hy : y ∈ DarbouxRS.subinterval P i)
    (hz : z ∈ DarbouxRS.subinterval P i)
    (hyz : eta ≤ |f y - f z|) :
    eta ≤ DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i := by
  have hcellBelow : BddBelow (f '' DarbouxRS.subinterval P i) :=
    BddBelow.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hBelow
  have hcellAbove : BddAbove (f '' DarbouxRS.subinterval P i) :=
    BddAbove.mono (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P hi)) hAbove
  have hlow_y : DarbouxRS.lowerStep P f i ≤ f y := by
    unfold DarbouxRS.lowerStep
    exact csInf_le hcellBelow ⟨y, hy, rfl⟩
  have hlow_z : DarbouxRS.lowerStep P f i ≤ f z := by
    unfold DarbouxRS.lowerStep
    exact csInf_le hcellBelow ⟨z, hz, rfl⟩
  have hy_up : f y ≤ DarbouxRS.upperStep P f i := by
    unfold DarbouxRS.upperStep
    exact le_csSup hcellAbove ⟨y, hy, rfl⟩
  have hz_up : f z ≤ DarbouxRS.upperStep P f i := by
    unfold DarbouxRS.upperStep
    exact le_csSup hcellAbove ⟨z, hz, rfl⟩
  have hpos :
      f y - f z ≤ DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i := by
    linarith
  have hneg :
      -(DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) ≤ f y - f z := by
    linarith
  exact le_trans hyz (abs_le.mpr ⟨hneg, hpos⟩)

theorem prob_7_3_adjacent_cell_oscillation_lower_bound_of_endpoint_split
    {a b eta : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ} (hiNext : i + 1 < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    {y z : ℝ}
    (hy : y ∈ DarbouxRS.subinterval P i)
    (hz : z ∈ DarbouxRS.subinterval P (i + 1))
    (hyz : eta ≤ |f y - f z|) :
    eta ≤
      (DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) +
      (DarbouxRS.upperStep P f (i + 1) - DarbouxRS.lowerStep P f (i + 1)) := by
  let c : ℝ := P.pts (i + 1)
  have hi : i < P.n := Nat.lt_trans (Nat.lt_succ_self i) hiNext
  have hc_i : c ∈ DarbouxRS.subinterval P i := by
    dsimp [c, DarbouxRS.subinterval]
    exact ⟨le_of_lt (P.strict_mono i hi), le_rfl⟩
  have hc_next : c ∈ DarbouxRS.subinterval P (i + 1) := by
    dsimp [c, DarbouxRS.subinterval]
    exact ⟨le_rfl, le_of_lt (P.strict_mono (i + 1) hiNext)⟩
  have hyc :
      |f y - f c| ≤ DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i := by
    exact prob_7_3_cell_oscillation_lower_bound_of_two_points
      (P := P) (i := i) hi hAbove hBelow hy hc_i le_rfl
  have hcz :
      |f c - f z| ≤
        DarbouxRS.upperStep P f (i + 1) - DarbouxRS.lowerStep P f (i + 1) := by
    exact prob_7_3_cell_oscillation_lower_bound_of_two_points
      (P := P) (i := i + 1) hiNext hAbove hBelow hc_next hz le_rfl
  have htri : |f y - f z| ≤ |f y - f c| + |f c - f z| := by
    calc
      |f y - f z| = |(f y - f c) + (f c - f z)| := by ring_nf
      _ ≤ |f y - f c| + |f c - f z| := abs_add_le _ _
  linarith

theorem prob_7_3_adjacent_pair_oscillation_lower_bound_of_mem_union
    {a b eta : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ} (hiNext : i + 1 < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    {y z : ℝ}
    (hy : y ∈ DarbouxRS.subinterval P i ∪ DarbouxRS.subinterval P (i + 1))
    (hz : z ∈ DarbouxRS.subinterval P i ∪ DarbouxRS.subinterval P (i + 1))
    (hyz : eta ≤ |f y - f z|) :
    eta ≤
      (DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) +
      (DarbouxRS.upperStep P f (i + 1) - DarbouxRS.lowerStep P f (i + 1)) := by
  have hi : i < P.n := Nat.lt_trans (Nat.lt_succ_self i) hiNext
  have hgap_i_nonneg :
      0 ≤ DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i := by
    have hle := DarbouxRS.lowerStep_le_upperStep_core
      (P := P) (i := i) hi hBelow hAbove
    linarith
  have hgap_next_nonneg :
      0 ≤ DarbouxRS.upperStep P f (i + 1) - DarbouxRS.lowerStep P f (i + 1) := by
    have hle := DarbouxRS.lowerStep_le_upperStep_core
      (P := P) (i := i + 1) hiNext hBelow hAbove
    linarith
  rcases hy with hyLeft | hyRight
  · rcases hz with hzLeft | hzRight
    · have hcell := prob_7_3_cell_oscillation_lower_bound_of_two_points
        (P := P) (i := i) hi hAbove hBelow hyLeft hzLeft hyz
      linarith
    · exact prob_7_3_adjacent_cell_oscillation_lower_bound_of_endpoint_split
        (P := P) (i := i) hiNext hAbove hBelow hyLeft hzRight hyz
  · rcases hz with hzLeft | hzRight
    · have hyz' : eta ≤ |f z - f y| := by
        simpa [abs_sub_comm] using hyz
      exact prob_7_3_adjacent_cell_oscillation_lower_bound_of_endpoint_split
        (P := P) (i := i) hiNext hAbove hBelow hzLeft hyRight hyz'
    · have hcell := prob_7_3_cell_oscillation_lower_bound_of_two_points
        (P := P) (i := i + 1) hiNext hAbove hBelow hyRight hzRight hyz
      linarith

theorem prob_7_3_largeOscillation_point_forces_protected_cell_gap
    {a b : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) {i n : ℕ} (hi : i < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    {x r : ℝ}
    (hx : x ∈ prob_7_3_largeOscillationSet f a b n)
    (hr : 0 < r)
    (hball : ∀ y : ℝ, y ∈ Icc a b → |y - x| < r →
      y ∈ DarbouxRS.subinterval P i) :
    (1 : ℝ) / ((n : ℝ) + 1) ≤
      DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i := by
  rcases hx with ⟨_hxI, _heta, hlocal⟩
  rcases hlocal r hr with ⟨y, hyI, hydist, z, hzI, hzdist, hyz⟩
  exact prob_7_3_cell_oscillation_lower_bound_of_two_points
    (P := P) hi hAbove hBelow
    (hball y hyI hydist) (hball z hzI hzdist) hyz

theorem prob_7_3_largeOscillation_point_forces_adjacent_union_gap
    {a b : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) {i n : ℕ} (hiNext : i + 1 < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    {x r : ℝ}
    (hx : x ∈ prob_7_3_largeOscillationSet f a b n)
    (hr : 0 < r)
    (hball : ∀ y : ℝ, y ∈ Icc a b → |y - x| < r →
      y ∈ DarbouxRS.subinterval P i ∪ DarbouxRS.subinterval P (i + 1)) :
    (1 : ℝ) / ((n : ℝ) + 1) ≤
      (DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) +
      (DarbouxRS.upperStep P f (i + 1) - DarbouxRS.lowerStep P f (i + 1)) := by
  rcases hx with ⟨_hxI, _heta, hlocal⟩
  rcases hlocal r hr with ⟨y, hyI, hydist, z, hzI, hzdist, hyz⟩
  exact prob_7_3_adjacent_pair_oscillation_lower_bound_of_mem_union
    (P := P) (i := i) hiNext hAbove hBelow
    (hball y hyI hydist) (hball z hzI hzdist) hyz

theorem prob_7_3_weighted_cell_oscillation_lower_bound_of_two_points
    (F : StieltjesFunction ℝ) {a b eta : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) {i : ℕ} (hi : i < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    {y z : ℝ}
    (hy : y ∈ DarbouxRS.subinterval P i)
    (hz : z ∈ DarbouxRS.subinterval P i)
    (hyz : eta ≤ |f y - f z|) :
    eta * (F (P.pts (i + 1)) - F (P.pts i)) ≤
      (DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) *
        (F (P.pts (i + 1)) - F (P.pts i)) := by
  have hcell :
      eta ≤ DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i :=
    prob_7_3_cell_oscillation_lower_bound_of_two_points
      (P := P) hi hAbove hBelow hy hz hyz
  have hinc : 0 ≤ F (P.pts (i + 1)) - F (P.pts i) := by
    exact sub_nonneg.mpr (F.mono (le_of_lt (P.strict_mono i hi)))
  exact mul_le_mul_of_nonneg_right hcell hinc

theorem prob_7_3_largeOscillation_point_forces_weighted_protected_cell_gap
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) {i n : ℕ} (hi : i < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    {x r : ℝ}
    (hx : x ∈ prob_7_3_largeOscillationSet f a b n)
    (hr : 0 < r)
    (hball : ∀ y : ℝ, y ∈ Icc a b → |y - x| < r →
      y ∈ DarbouxRS.subinterval P i) :
    ((1 : ℝ) / ((n : ℝ) + 1)) *
        (F (P.pts (i + 1)) - F (P.pts i)) ≤
      (DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) *
        (F (P.pts (i + 1)) - F (P.pts i)) := by
  have hcell :
      (1 : ℝ) / ((n : ℝ) + 1) ≤
        DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i :=
    prob_7_3_largeOscillation_point_forces_protected_cell_gap
      (P := P) hi hAbove hBelow hx hr hball
  have hinc : 0 ≤ F (P.pts (i + 1)) - F (P.pts i) := by
    exact sub_nonneg.mpr (F.mono (le_of_lt (P.strict_mono i hi)))
  exact mul_le_mul_of_nonneg_right hcell hinc

theorem prob_7_3_finset_weighted_cell_lower_bound
    (F : StieltjesFunction ℝ) {a b eta : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) (S : Finset ℕ)
    (hcell : ∀ i ∈ S,
      eta * (F (P.pts (i + 1)) - F (P.pts i)) ≤
        (DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) *
          (F (P.pts (i + 1)) - F (P.pts i))) :
    eta * (∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i))) ≤
      ∑ i ∈ S,
        (DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) *
          (F (P.pts (i + 1)) - F (P.pts i)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum hcell

theorem prob_7_3_finset_weighted_cell_lower_bound_partitionOscillation
    (F : StieltjesFunction ℝ) {a b eta : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hcell : ∀ i ∈ S,
      eta ≤ DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) :
    eta * (∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i))) ≤
      Thm11SourceRoute.partitionOscillation P f F := by
  have hcellWeighted : ∀ i ∈ S,
      eta * (F (P.pts (i + 1)) - F (P.pts i)) ≤
        (DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) *
          (F (P.pts (i + 1)) - F (P.pts i)) := by
    intro i hiS
    have hinc : 0 ≤ F (P.pts (i + 1)) - F (P.pts i) := by
      exact sub_nonneg.mpr (F.mono (le_of_lt (P.strict_mono i (hS i hiS))))
    exact mul_le_mul_of_nonneg_right (hcell i hiS) hinc
  have hsum :=
    prob_7_3_finset_weighted_cell_lower_bound
      (F := F) (P := P) (S := S) (eta := eta) (f := f) hcellWeighted
  refine le_trans hsum ?_
  unfold Thm11SourceRoute.partitionOscillation
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro i hiS
    exact Finset.mem_range.mpr (hS i hiS)
  · intro i _hiRange _hiNotS
    have hi : i < P.n := Finset.mem_range.mp _hiRange
    have hgap : 0 ≤ DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i := by
      have hle := DarbouxRS.lowerStep_le_upperStep_core
        (P := P) (i := i) hi hBelow hAbove
      linarith
    have hinc : 0 ≤ F (P.pts (i + 1)) - F (P.pts i) := by
      exact sub_nonneg.mpr (F.mono (le_of_lt (P.strict_mono i hi)))
    exact mul_nonneg hgap hinc

theorem prob_7_3_restricted_measure_partition_cell_ne_top
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    {i : ℕ} (hi : i < P.n) :
    (F.measure.restrict (Icc a b)) (Ioc (P.pts i) (P.pts (i + 1))) ≠ ⊤ := by
  rw [Measure.restrict_apply measurableSet_Ioc]
  have hcell_subset :
      Ioc (P.pts i) (P.pts (i + 1)) ⊆ Icc a b :=
    thm_7_8_partition_Ioc_subset_Icc P hi
  have hcell_inter :
      Ioc (P.pts i) (P.pts (i + 1)) ∩ Icc a b =
        Ioc (P.pts i) (P.pts (i + 1)) := by
    exact inter_eq_self_of_subset_left hcell_subset
  rw [hcell_inter]
  rw [F.measure_Ioc]
  exact ENNReal.ofReal_ne_top

theorem prob_7_3_restricted_measure_finset_partition_cells_toReal_le_sum
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (S : Finset ℕ) (hS : ∀ i ∈ S, i < P.n) :
    ((F.measure.restrict (Icc a b))
        (⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)))).toReal ≤
      ∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i)) := by
  let μr : Measure ℝ := F.measure.restrict (Icc a b)
  let cell : ℕ → Set ℝ := fun i => Ioc (P.pts i) (P.pts (i + 1))
  have hle :
      μr (⋃ i ∈ S, cell i) ≤ ∑ i ∈ S, μr (cell i) := by
    exact measure_biUnion_finset_le S cell
  have hsum_ne_top : (∑ i ∈ S, μr (cell i)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro i hi
    exact prob_7_3_restricted_measure_partition_cell_ne_top
      (F := F) (P := P) (i := i) (hS i hi)
  have hto : (μr (⋃ i ∈ S, cell i)).toReal ≤ (∑ i ∈ S, μr (cell i)).toReal :=
    ENNReal.toReal_mono hsum_ne_top hle
  calc
    ((F.measure.restrict (Icc a b))
        (⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)))).toReal =
        (μr (⋃ i ∈ S, cell i)).toReal := by rfl
    _ ≤ (∑ i ∈ S, μr (cell i)).toReal := hto
    _ = ∑ i ∈ S, (μr (cell i)).toReal := by
      rw [ENNReal.toReal_sum]
      intro i hi
      exact prob_7_3_restricted_measure_partition_cell_ne_top
        (F := F) (P := P) (i := i) (hS i hi)
    _ = ∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact prob_7_3_restricted_measure_partition_cell_toReal
        (F := F) (P := P) (i := i) (hS i hi)

theorem prob_7_3_partition_Ioc_cells_pairwiseDisjoint
    {a b : ℝ} (P : DarbouxRS.Partition a b)
    (S : Finset ℕ) (hS : ∀ i ∈ S, i < P.n) :
    (S : Set ℕ).PairwiseDisjoint
      (fun i : ℕ => Ioc (P.pts i) (P.pts (i + 1))) := by
  rw [Set.PairwiseDisjoint]
  intro i hiS j hjS hij
  change Disjoint
    (Ioc (P.pts i) (P.pts (i + 1)))
    (Ioc (P.pts j) (P.pts (j + 1)))
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact thm_7_8_partition_Ioc_disjoint_at
    P (hS i hiS) (hS j hjS) hij.symm hxi hxj

theorem prob_7_3_restricted_measure_finset_partition_cells_sum_eq_toReal_union
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (S : Finset ℕ) (hS : ∀ i ∈ S, i < P.n) :
    ∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i)) =
      ((F.measure.restrict (Icc a b))
        (⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)))).toReal := by
  let μr : Measure ℝ := F.measure.restrict (Icc a b)
  let cell : ℕ → Set ℝ := fun i => Ioc (P.pts i) (P.pts (i + 1))
  have hmeasure_eq :
      μr (⋃ i ∈ S, cell i) = ∑ i ∈ S, μr (cell i) := by
    exact MeasureTheory.measure_biUnion_finset
      (prob_7_3_partition_Ioc_cells_pairwiseDisjoint P S hS)
      (fun _ _ => measurableSet_Ioc)
  calc
    ∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i))
        = ∑ i ∈ S, (μr (cell i)).toReal := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            exact prob_7_3_restricted_measure_partition_cell_toReal
              (F := F) (P := P) (i := i) (hS i hi)
    _ = (∑ i ∈ S, μr (cell i)).toReal := by
          rw [ENNReal.toReal_sum]
          intro i hi
          exact prob_7_3_restricted_measure_partition_cell_ne_top
            (F := F) (P := P) (i := i) (hS i hi)
    _ = (μr (⋃ i ∈ S, cell i)).toReal := by rw [hmeasure_eq]

theorem prob_7_3_partition_cell_increment_sum_le_open_measure_toReal
    (F : StieltjesFunction ℝ) {a b : ℝ} (P : DarbouxRS.Partition a b)
    (S : Finset ℕ) (hS : ∀ i ∈ S, i < P.n) {G : Set ℝ}
    (hcellSub : ∀ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)) ⊆ G) :
    ∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i)) ≤
      (((F.measure.restrict (Icc a b)) G).toReal) := by
  let μr : Measure ℝ := F.measure.restrict (Icc a b)
  let cell : ℕ → Set ℝ := fun i => Ioc (P.pts i) (P.pts (i + 1))
  have hUnionSub : (⋃ i ∈ S, cell i) ⊆ G := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨i, hxi⟩
    rcases mem_iUnion.mp hxi with ⟨hiS, hxcell⟩
    exact hcellSub i hiS hxcell
  haveI : IsFiniteMeasure μr := prob_7_3_isFiniteMeasure_restrict_Icc F
  have hG_ne_top : μr G ≠ ⊤ := measure_ne_top μr G
  have hto :
      (μr (⋃ i ∈ S, cell i)).toReal ≤ (μr G).toReal :=
    ENNReal.toReal_mono hG_ne_top (measure_mono hUnionSub)
  have hsum_eq :
      ∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i)) =
        (μr (⋃ i ∈ S, cell i)).toReal := by
    exact prob_7_3_restricted_measure_finset_partition_cells_sum_eq_toReal_union
      (F := F) (P := P) (S := S) hS
  simpa [μr, cell] using hsum_eq.trans_le hto

theorem prob_7_3_covered_set_forces_partitionOscillation_lower_bound
    (F : StieltjesFunction ℝ) {a b eta : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) (S : Finset ℕ) {K : Set ℝ}
    (heta : 0 ≤ eta)
    (hS : ∀ i ∈ S, i < P.n)
    (hKcover : K ⊆ ⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)))
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hcell : ∀ i ∈ S,
      eta ≤ DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i) :
    eta * (((F.measure.restrict (Icc a b)) K).toReal) ≤
      Thm11SourceRoute.partitionOscillation P f F := by
  let μr : Measure ℝ := F.measure.restrict (Icc a b)
  let cell : ℕ → Set ℝ := fun i => Ioc (P.pts i) (P.pts (i + 1))
  have hUnionToReal :
      (μr (⋃ i ∈ S, cell i)).toReal ≤
        ∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i)) := by
    exact prob_7_3_restricted_measure_finset_partition_cells_toReal_le_sum
      (F := F) (P := P) (S := S) hS
  have hleUnionSum :
      μr (⋃ i ∈ S, cell i) ≤ ∑ i ∈ S, μr (cell i) := by
    exact measure_biUnion_finset_le S cell
  have hsum_ne_top : (∑ i ∈ S, μr (cell i)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro i hi
    exact prob_7_3_restricted_measure_partition_cell_ne_top
      (F := F) (P := P) (i := i) (hS i hi)
  have hUnion_ne_top : μr (⋃ i ∈ S, cell i) ≠ ⊤ :=
    (lt_of_le_of_lt hleUnionSum hsum_ne_top.lt_top).ne
  have hKToRealLeUnion : (μr K).toReal ≤ (μr (⋃ i ∈ S, cell i)).toReal :=
    ENNReal.toReal_mono hUnion_ne_top (measure_mono hKcover)
  have hKToRealLeSum :
      (μr K).toReal ≤
        ∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i)) :=
    le_trans hKToRealLeUnion hUnionToReal
  have hmul :
      eta * (μr K).toReal ≤
        eta * (∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i))) :=
    mul_le_mul_of_nonneg_left hKToRealLeSum heta
  have hosc :
      eta * (∑ i ∈ S, (F (P.pts (i + 1)) - F (P.pts i))) ≤
        Thm11SourceRoute.partitionOscillation P f F :=
    prob_7_3_finset_weighted_cell_lower_bound_partitionOscillation
      (F := F) (P := P) (S := S) hS hAbove hBelow hcell
  exact le_trans hmul hosc

theorem prob_7_3_protected_largeOscillation_cell_cover_forces_partitionOscillation_lower_bound
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) (S : Finset ℕ) {K : Set ℝ} (n : ℕ)
    (hS : ∀ i ∈ S, i < P.n)
    (hKcover : K ⊆ ⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)))
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hprotected : ∀ i ∈ S, ∃ x r : ℝ,
      x ∈ prob_7_3_largeOscillationSet f a b n ∧
        0 < r ∧
        ∀ y : ℝ, y ∈ Icc a b → |y - x| < r →
          y ∈ DarbouxRS.subinterval P i) :
    ((1 : ℝ) / ((n : ℝ) + 1)) *
        (((F.measure.restrict (Icc a b)) K).toReal) ≤
      Thm11SourceRoute.partitionOscillation P f F := by
  have heta : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
  refine prob_7_3_covered_set_forces_partitionOscillation_lower_bound
    (F := F) (P := P) (S := S) (K := K)
    (eta := (1 : ℝ) / ((n : ℝ) + 1)) heta hS hKcover hAbove hBelow ?_
  intro i hiS
  rcases hprotected i hiS with ⟨x, r, hx, hr, hball⟩
  exact prob_7_3_largeOscillation_point_forces_protected_cell_gap
    (P := P) (i := i) (n := n) (hS i hiS) hAbove hBelow hx hr hball

theorem prob_7_3_gapSmall_excludes_fine_partitionOscillation_lower_bound
    (F : StieltjesFunction ℝ) {a b eta : ℝ} {f : ℝ → ℝ} {K : Set ℝ}
    (hgap : Thm11SourceRoute.ClosedIntervalDarbouxGapSmall a b f F)
    (hpos : 0 < eta * (((F.measure.restrict (Icc a b)) K).toReal)) :
    ∃ δ > 0, ∀ P : DarbouxRS.Partition a b, P.mesh < δ →
      ¬ eta * (((F.measure.restrict (Icc a b)) K).toReal) ≤
          Thm11SourceRoute.partitionOscillation P f F := by
  have hhalf : 0 < (eta * (((F.measure.restrict (Icc a b)) K).toReal)) / 2 := by
    linarith
  rcases hgap
      ((eta * (((F.measure.restrict (Icc a b)) K).toReal)) / 2) hhalf with
    ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh hlower
  have hgapP := Hδ P hmesh
  rw [Thm11SourceRoute.upperSum_sub_lowerSum_eq_partitionOscillation] at hgapP
  linarith

theorem prob_7_3_gapSmall_excludes_fine_protected_largeOscillation_cell_cover
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ} (n : ℕ)
    (hgap : Thm11SourceRoute.ClosedIntervalDarbouxGapSmall a b f F)
    (hpos :
      0 < ((1 : ℝ) / ((n : ℝ) + 1)) *
        (((F.measure.restrict (Icc a b)) K).toReal)) :
    ∃ δ > 0, ∀ P : DarbouxRS.Partition a b, P.mesh < δ →
      ∀ S : Finset ℕ,
        (∀ i ∈ S, i < P.n) →
        K ⊆ ⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)) →
        BddAbove (f '' Icc a b) →
        BddBelow (f '' Icc a b) →
        (∀ i ∈ S, ∃ x r : ℝ,
          x ∈ prob_7_3_largeOscillationSet f a b n ∧
            0 < r ∧
            ∀ y : ℝ, y ∈ Icc a b → |y - x| < r →
              y ∈ DarbouxRS.subinterval P i) →
        False := by
  rcases prob_7_3_gapSmall_excludes_fine_partitionOscillation_lower_bound
      (F := F) (eta := (1 : ℝ) / ((n : ℝ) + 1)) (K := K) hgap hpos with
    ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh S hS hKcover hAbove hBelow hprotected
  exact Hδ P hmesh
    (prob_7_3_protected_largeOscillation_cell_cover_forces_partitionOscillation_lower_bound
      (F := F) (P := P) (S := S) (K := K) n hS hKcover hAbove hBelow hprotected)

theorem prob_7_3_restricted_measure_diff_left_endpoint_toReal_eq
    (μ : Measure ℝ) {a b : ℝ} (K : Set ℝ)
    (hAtom : (μ.restrict (Icc a b)) {a} = 0) :
    ((μ.restrict (Icc a b)) (K \ {a})).toReal =
      ((μ.restrict (Icc a b)) K).toReal := by
  rw [measure_diff_null hAtom]

theorem prob_7_3_restricted_stieltjes_measure_diff_left_endpoint_toReal_eq
    (F : StieltjesFunction ℝ) {a b : ℝ} (K : Set ℝ)
    (hAtom : F.measure {a} = 0) :
    (((F.measure.restrict (Icc a b)) (K \ {a})).toReal) =
      (((F.measure.restrict (Icc a b)) K).toReal) := by
  exact prob_7_3_restricted_measure_diff_left_endpoint_toReal_eq
    (μ := F.measure) (a := a) (b := b) K
    (prob_7_3_endpoint_atom_convention_support F hAtom)

theorem prob_7_3_gapSmall_excludes_fine_protected_largeOscillation_cell_cover_off_left
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ} {K : Set ℝ} (n : ℕ)
    (hgap : Thm11SourceRoute.ClosedIntervalDarbouxGapSmall a b f F)
    (hAtom : F.measure {a} = 0)
    (hpos :
      0 < ((1 : ℝ) / ((n : ℝ) + 1)) *
        (((F.measure.restrict (Icc a b)) K).toReal)) :
    ∃ δ > 0, ∀ P : DarbouxRS.Partition a b, P.mesh < δ →
      ∀ S : Finset ℕ,
        (∀ i ∈ S, i < P.n) →
        K \ {a} ⊆ ⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)) →
        BddAbove (f '' Icc a b) →
        BddBelow (f '' Icc a b) →
        (∀ i ∈ S, ∃ x r : ℝ,
          x ∈ prob_7_3_largeOscillationSet f a b n ∧
            0 < r ∧
            ∀ y : ℝ, y ∈ Icc a b → |y - x| < r →
              y ∈ DarbouxRS.subinterval P i) →
        False := by
  have hpos' :
      0 < ((1 : ℝ) / ((n : ℝ) + 1)) *
        (((F.measure.restrict (Icc a b)) (K \ {a})).toReal) := by
    rw [prob_7_3_restricted_stieltjes_measure_diff_left_endpoint_toReal_eq
      (F := F) (K := K) hAtom]
    exact hpos
  exact prob_7_3_gapSmall_excludes_fine_protected_largeOscillation_cell_cover
    (F := F) (K := K \ {a}) n hgap hpos'

theorem prob_7_3_rsIntegrable_forces_largeOscillationSet_null
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ} (n : ℕ)
    (hab : a < b)
    (hAtom : F.measure {a} = 0)
    (hBounded : ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M)
    (hRS : RSIntegrable f F a b) :
    (F.measure.restrict (Icc a b)) (prob_7_3_largeOscillationSet f a b n) = 0 := by
  classical
  let μr : Measure ℝ := F.measure.restrict (Icc a b)
  letI : IsFiniteMeasure μr := prob_7_3_isFiniteMeasure_restrict_Icc (a := a) (b := b) F
  by_contra hne
  have hposLayer :
      0 < (μr (prob_7_3_largeOscillationSet f a b n)).toReal := by
    have hne' : μr (prob_7_3_largeOscillationSet f a b n) ≠ 0 := by
      simpa [μr] using hne
    have hlt_top : μr (prob_7_3_largeOscillationSet f a b n) < ⊤ := by
      exact measure_lt_top μr _
    exact ENNReal.toReal_pos hne' hlt_top.ne
  rcases prob_7_3_exists_compact_subset_largeOscillationSet_off_left_pos
      (F := F) (a := a) (b := b) (f := f) n hAtom (by simpa [μr] using hposLayer) with
    ⟨K, hKcompact, hKsub, haK, hKpos⟩
  have hgap : Thm11SourceRoute.ClosedIntervalDarbouxGapSmall a b f F :=
    prob_7_3_darbouxGapSmall_of_rsIntegrable hRS
  rcases prob_7_3_bddAbove_bddBelow_of_abs_bound
      (a := a) (b := b) (f := f) hBounded with
    ⟨hAbove, hBelow⟩
  let eta : ℝ := (1 : ℝ) / ((n : ℝ) + 1)
  have heta_nonneg : 0 ≤ eta := by
    dsimp [eta]
    positivity
  have hposWeighted : 0 < eta * (μr K).toReal := by
    have heta_pos : 0 < eta := by
      dsimp [eta]
      positivity
    exact mul_pos heta_pos (by simpa [μr] using hKpos)
  rcases prob_7_3_gapSmall_excludes_fine_partitionOscillation_lower_bound
      (F := F) (a := a) (b := b) (f := f) (eta := eta) (K := K)
      hgap hposWeighted with
    ⟨δ, hδ, Hδ⟩
  rcases prob_7_3_exists_fine_partition_atom_free_internal_endpoints
      (F := F) (a := a) (b := b) hab hδ with
    ⟨P, hmesh, B, hInternal, _hBIoo, _hBsingleNull, hBnull⟩
  rcases prob_7_3_partition_cells_cover_compact_diff_atom_free_endpoints
      (a := a) (b := b) (f := f) n P B hKsub haK hInternal with
    ⟨S, hS, hKcover, hprotected⟩
  have htoReal :
      (((F.measure.restrict (Icc a b)) (K \ (B : Set ℝ))).toReal) =
        (((F.measure.restrict (Icc a b)) K).toReal) :=
    prob_7_3_restricted_measure_diff_atom_free_endpoint_finset_toReal_eq
      (F := F) (a := a) (b := b) K B hBnull
  have hlower' :
      eta * (((F.measure.restrict (Icc a b)) (K \ (B : Set ℝ))).toReal) ≤
        Thm11SourceRoute.partitionOscillation P f F := by
    simpa [eta] using
      prob_7_3_protected_largeOscillation_cell_cover_forces_partitionOscillation_lower_bound
        (F := F) (P := P) (S := S) (K := K \ (B : Set ℝ)) n
        hS hKcover hAbove hBelow hprotected
  have hlower :
      eta * (((F.measure.restrict (Icc a b)) K).toReal) ≤
        Thm11SourceRoute.partitionOscillation P f F := by
    rw [← htoReal]
    exact hlower'
  exact Hδ P hmesh hlower

theorem prob_7_3_rsIntegrable_implies_ae_continuity
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b)
    (hAtom : F.measure {a} = 0)
    (hBounded : ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M)
    (hRS : RSIntegrable f F a b) :
    ∀ᵐ x ∂(F.measure.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x := by
  refine prob_7_3_largeOscillationSet_nulls_imply_ae_continuity
    (μ := F.measure) (a := a) (b := b) (f := f) ?_
  intro n
  exact prob_7_3_rsIntegrable_forces_largeOscillationSet_null
    (F := F) (a := a) (b := b) (f := f) n hab hAtom hBounded hRS

