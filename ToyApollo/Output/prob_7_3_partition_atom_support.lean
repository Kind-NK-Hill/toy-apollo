import ToyApollo.Output.prob_7_3_oscillation_support

open MeasureTheory Set Filter

noncomputable section

theorem prob_7_3_exists_fine_partition_atom_free_internal_endpoints_for_measure
    (μ : Measure ℝ) [SFinite μ] {a b δ : ℝ}
    (hab : a < b) (hδ : 0 < δ) :
    ∃ P : DarbouxRS.Partition a b,
      P.mesh < δ ∧
      ∃ B : Finset ℝ,
        (∀ j : ℕ, 0 < j → j < P.n → P.pts j ∈ B) ∧
        (∀ x ∈ B, x ∈ Ioo a b) ∧
        (∀ x ∈ B, μ ({x} : Set ℝ) = 0) ∧
        μ (B : Set ℝ) = 0 := by
  classical
  let C : Set ℝ := {x : ℝ | μ ({x} : Set ℝ) ≠ 0}
  have hCcount : C.Countable := by
    have hpos : Set.Countable {x : ℝ | 0 < μ ({x} : Set ℝ)} := by
      refine Measure.countable_meas_pos_of_disjoint_iUnion
        (μ := μ) (As := fun x : ℝ => ({x} : Set ℝ)) ?_ ?_
      · intro x
        exact measurableSet_singleton x
      · intro x y hxy
        exact disjoint_singleton.mpr hxy
    refine hpos.mono ?_
    intro x hx
    exact lt_of_le_of_ne (zero_le _) (Ne.symm hx)
  have hCdense : Dense Cᶜ := hCcount.dense_compl ℝ
  obtain ⟨N, hNbig⟩ := exists_nat_gt (max ((3 * (b - a)) / (2 * δ)) 2)
  have hNgt2R : (2 : ℝ) < (N : ℝ) := lt_of_le_of_lt (le_max_right _ _) hNbig
  have hNpos : 0 < N := by
    exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 2) hNgt2R)
  have hNgt1 : 1 < N := by
    exact_mod_cast (lt_trans (by norm_num : (1 : ℝ) < 2) hNgt2R)
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast hNpos
  let h : ℝ := (b - a) / (N : ℝ)
  have hhpos : 0 < h := by
    exact div_pos (sub_pos.mpr hab) hNposR
  have hmeshSmall : 3 * h / 2 < δ := by
    have hltN : (3 * (b - a)) / (2 * δ) < (N : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hNbig
    have hmul : 3 * (b - a) < (N : ℝ) * (2 * δ) := by
      rwa [div_lt_iff₀ (by positivity : 0 < 2 * δ)] at hltN
    dsimp [h]
    field_simp [ne_of_gt hNposR]
    nlinarith
  let u : ℕ → ℝ := fun j => a + (j : ℝ) * h
  have hwindow : ∀ j : ℕ, u j - h / 4 < u j + h / 4 := by
    intro j
    linarith [hhpos]
  let pick : ℕ → ℝ := fun j =>
    Classical.choose (hCdense.exists_between (hwindow j))
  have hpick : ∀ j : ℕ,
      pick j ∈ Cᶜ ∧ u j - h / 4 < pick j ∧ pick j < u j + h / 4 := by
    intro j
    exact Classical.choose_spec (hCdense.exists_between (hwindow j))
  let pts : ℕ → ℝ := fun j =>
    if j = 0 then a else if j < N then pick j else b
  have hpts0 : pts 0 = a := by simp [pts]
  have hptsN : pts N = b := by
    simp [pts, ne_of_gt hNpos]
  have hpts_internal : ∀ j : ℕ, 0 < j → j < N → pts j = pick j := by
    intro j hj0 hjN
    simp [pts, ne_of_gt hj0, hjN]
  have hstrict : ∀ i, i < N → pts i < pts (i + 1) := by
    intro i hiN
    by_cases hi0 : i = 0
    · subst hi0
      have h1N : 1 < N := hNgt1
      have hp1 := hpick 1
      have hpts1 : pts 1 = pick 1 := hpts_internal 1 (by norm_num) h1N
      have hu1 : u 1 = a + h := by simp [u]
      rw [hpts0, hpts1]
      have : a < u 1 - h / 4 := by
        rw [hu1]
        linarith [hhpos]
      exact lt_trans this hp1.2.1
    · have hi0pos : 0 < i := Nat.pos_of_ne_zero hi0
      by_cases hlast : i + 1 = N
      · have hptsi : pts i = pick i := hpts_internal i hi0pos hiN
        have hptsn : pts (i + 1) = b := by
          rw [hlast]
          exact hptsN
        rw [hptsi, hptsn]
        have hpi := hpick i
        have hui : u i = b - h := by
          have hi_eq : (i : ℝ) = (N : ℝ) - 1 := by
            have hi_nat : i = N - 1 := by omega
            rw [hi_nat]
            have hNpos' : 0 < N := hNpos
            norm_num [Nat.cast_sub hNpos']
          dsimp [u, h]
          rw [hi_eq]
          field_simp [ne_of_gt hNposR]
          ring
        have : u i + h / 4 < b := by
          rw [hui]
          linarith [hhpos]
        exact lt_trans hpi.2.2 this
      · have hiplusN : i + 1 < N := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hiN) hlast
        have hptsi : pts i = pick i := hpts_internal i hi0pos hiN
        have hptsip : pts (i + 1) = pick (i + 1) :=
          hpts_internal (i + 1) (Nat.succ_pos i) hiplusN
        rw [hptsi, hptsip]
        have hpi := hpick i
        have hpip := hpick (i + 1)
        have hui : u (i + 1) = u i + h := by
          dsimp [u]
          norm_num [Nat.cast_add]
          ring
        have : u i + h / 4 < u (i + 1) - h / 4 := by
          rw [hui]
          linarith [hhpos]
        exact lt_trans hpi.2.2 (lt_trans this hpip.2.1)
  let P : DarbouxRS.Partition a b :=
    { n := N
      hn := hNpos
      pts := pts
      pts_start := hpts0
      pts_end := hptsN
      strict_mono := hstrict }
  have hmesh : P.mesh < δ := by
    rw [DarbouxRS.Partition.mesh]
    rw [Finset.sup'_lt_iff]
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    by_cases hi0 : i = 0
    · subst hi0
      have h1N : 1 < N := hNgt1
      have hp1 := hpick 1
      have hpts1 : pts 1 = pick 1 := hpts_internal 1 (by norm_num) h1N
      have hu1 : u 1 = a + h := by simp [u]
      dsimp [P]
      rw [hpts0, hpts1]
      have hle : pick 1 - a < 3 * h / 2 := by
        rw [hu1] at hp1
        linarith [hp1.2.2]
      exact lt_trans hle hmeshSmall
    · have hi0pos : 0 < i := Nat.pos_of_ne_zero hi0
      by_cases hlast : i + 1 = N
      · have hptsi : pts i = pick i := hpts_internal i hi0pos hiN
        have hptsn : pts (i + 1) = b := by
          rw [hlast]
          exact hptsN
        have hpi := hpick i
        have hui : u i = b - h := by
          have hi_eq : (i : ℝ) = (N : ℝ) - 1 := by
            have hi_nat : i = N - 1 := by omega
            rw [hi_nat]
            have hNpos' : 0 < N := hNpos
            norm_num [Nat.cast_sub hNpos']
          dsimp [u, h]
          rw [hi_eq]
          field_simp [ne_of_gt hNposR]
          ring
        dsimp [P]
        rw [hptsi, hptsn]
        have hle : b - pick i < 3 * h / 2 := by
          rw [hui] at hpi
          linarith [hpi.2.1]
        exact lt_trans hle hmeshSmall
      · have hiplusN : i + 1 < N := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hiN) hlast
        have hptsi : pts i = pick i := hpts_internal i hi0pos hiN
        have hptsip : pts (i + 1) = pick (i + 1) :=
          hpts_internal (i + 1) (Nat.succ_pos i) hiplusN
        have hpi := hpick i
        have hpip := hpick (i + 1)
        have hui : u (i + 1) = u i + h := by
          dsimp [u]
          norm_num [Nat.cast_add]
          ring
        dsimp [P]
        rw [hptsi, hptsip]
        have hle : pick (i + 1) - pick i < 3 * h / 2 := by
          rw [hui] at hpip
          linarith [hpi.2.1, hpip.2.2]
        exact lt_trans hle hmeshSmall
  let B : Finset ℝ := (Finset.range N).filter (fun j => 0 < j) |>.image pick
  refine ⟨P, hmesh, B, ?_, ?_, ?_, ?_⟩
  · intro j hj0 hjN
    dsimp [P] at hjN ⊢
    rw [hpts_internal j hj0 hjN]
    exact Finset.mem_image.mpr ⟨j, by simp [hjN, hj0], rfl⟩
  · intro x hxB
    rcases Finset.mem_image.mp hxB with ⟨j, hj, rfl⟩
    have hjN : j < N := by
      exact (Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
    have hj0 : 0 < j := (Finset.mem_filter.mp hj).2
    have hpj := hpick j
    constructor
    · have hlow : a < u j - h / 4 := by
        dsimp [u]
        have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj0
        nlinarith [hhpos]
      exact lt_trans hlow hpj.2.1
    · have hu_lt : u j + h / 4 < b := by
        dsimp [u, h]
        have hj_le : (j : ℝ) ≤ (N : ℝ) - 1 := by
          have hjsucc_le : j + 1 ≤ N := Nat.succ_le_of_lt hjN
          have hjsucc_leR : ((j + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
            exact_mod_cast hjsucc_le
          norm_num [Nat.cast_add] at hjsucc_leR
          linarith
        field_simp [ne_of_gt hNposR]
        nlinarith [sub_pos.mpr hab, hNposR, hj_le]
      exact lt_trans hpj.2.2 hu_lt
  · intro x hxB
    rcases Finset.mem_image.mp hxB with ⟨j, _hj, rfl⟩
    have hpj := hpick j
    have hnot : ¬ pick j ∈ C := hpj.1
    by_contra hne
    exact hnot hne
  · exact (measure_null_iff_singleton (Finset.countable_toSet B)).2 (by
      intro x hxB
      rcases Finset.mem_image.mp hxB with ⟨j, _hj, rfl⟩
      have hpj := hpick j
      have hnot : ¬ pick j ∈ C := hpj.1
      by_contra hne
      exact hnot hne)

theorem prob_7_3_exists_fine_partition_atom_free_internal_endpoints
    (F : StieltjesFunction ℝ) {a b δ : ℝ}
    (hab : a < b) (hδ : 0 < δ) :
    ∃ P : DarbouxRS.Partition a b,
      P.mesh < δ ∧
      ∃ B : Finset ℝ,
        (∀ j : ℕ, 0 < j → j < P.n → P.pts j ∈ B) ∧
        (∀ x ∈ B, x ∈ Ioo a b) ∧
        (∀ x ∈ B, (F.measure.restrict (Icc a b)) ({x} : Set ℝ) = 0) ∧
        (F.measure.restrict (Icc a b)) (B : Set ℝ) = 0 := by
  let μ : Measure ℝ := F.measure.restrict (Icc a b)
  letI : IsFiniteMeasure μ := prob_7_3_isFiniteMeasure_restrict_Icc (a := a) (b := b) F
  exact
    prob_7_3_exists_fine_partition_atom_free_internal_endpoints_for_measure
      (μ := μ) hab hδ

theorem prob_7_3_restricted_measure_diff_atom_free_endpoint_finset_toReal_eq
    (F : StieltjesFunction ℝ) {a b : ℝ} (K : Set ℝ) (B : Finset ℝ)
    (hBnull : (F.measure.restrict (Icc a b)) (B : Set ℝ) = 0) :
    (((F.measure.restrict (Icc a b)) (K \ (B : Set ℝ))).toReal) =
      (((F.measure.restrict (Icc a b)) K).toReal) := by
  rw [measure_diff_null hBnull]

theorem prob_7_3_partition_cells_cover_compact_diff_atom_free_endpoints
    {a b : ℝ} {f : ℝ → ℝ} (n : ℕ)
    (P : DarbouxRS.Partition a b) (B : Finset ℝ) {K : Set ℝ}
    (hKsub : K ⊆ prob_7_3_largeOscillationSet f a b n)
    (haK : a ∉ K)
    (hInternal : ∀ j : ℕ, 0 < j → j < P.n → P.pts j ∈ B) :
    ∃ S : Finset ℕ,
      (∀ i ∈ S, i < P.n) ∧
      K \ (B : Set ℝ) ⊆
        ⋃ i ∈ S, Ioc (P.pts i) (P.pts (i + 1)) ∧
      (∀ i ∈ S, ∃ x r : ℝ,
        x ∈ prob_7_3_largeOscillationSet f a b n ∧
          0 < r ∧
          ∀ y : ℝ, y ∈ Icc a b → |y - x| < r →
            y ∈ DarbouxRS.subinterval P i) := by
  classical
  let S : Finset ℕ :=
    (Finset.range P.n).filter fun i =>
      ((K \ (B : Set ℝ)) ∩ Ioc (P.pts i) (P.pts (i + 1))).Nonempty
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i hiS
    exact Finset.mem_range.mp (Finset.mem_filter.mp hiS).1
  · intro x hxKdiff
    have hxK : x ∈ K := hxKdiff.1
    have hxLarge : x ∈ prob_7_3_largeOscillationSet f a b n := hKsub hxK
    have hxI : x ∈ Icc a b := hxLarge.1
    have hxne : x ≠ a := by
      intro hxa
      exact haK (by simpa [hxa] using hxK)
    rcases thm_7_8_partition_Ioc_cover_Icc_of_ne_left P hxI hxne with
      ⟨i, hi, hxcell⟩
    rw [mem_iUnion]
    refine ⟨i, ?_⟩
    rw [mem_iUnion]
    refine ⟨?_, hxcell⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hi, ⟨x, hxKdiff, hxcell⟩⟩
  · intro i hiS
    have hi : i < P.n := Finset.mem_range.mp (Finset.mem_filter.mp hiS).1
    rcases (Finset.mem_filter.mp hiS).2 with ⟨x, hxKdiff, hxcell⟩
    have hxK : x ∈ K := hxKdiff.1
    have hxnotB : x ∉ (B : Set ℝ) := hxKdiff.2
    have hxLarge : x ∈ prob_7_3_largeOscillationSet f a b n := hKsub hxK
    rcases lt_or_eq_of_le hxcell.2 with hxright | hxright
    · let r : ℝ := min (x - P.pts i) (P.pts (i + 1) - x) / 2
      have hleftgap : 0 < x - P.pts i := sub_pos.mpr hxcell.1
      have hrightgap : 0 < P.pts (i + 1) - x := sub_pos.mpr hxright
      have hr : 0 < r := by
        dsimp [r]
        exact half_pos (lt_min hleftgap hrightgap)
      refine ⟨x, r, hxLarge, hr, ?_⟩
      intro y _hyI hydist
      have hr_le_left : r ≤ x - P.pts i := by
        dsimp [r]
        exact (half_le_self (le_of_lt (lt_min hleftgap hrightgap))).trans (min_le_left _ _)
      have hr_le_right : r ≤ P.pts (i + 1) - x := by
        dsimp [r]
        exact (half_le_self (le_of_lt (lt_min hleftgap hrightgap))).trans (min_le_right _ _)
      have hy_left_lt : P.pts i < y := by
        have hxy : x - y < r := by
          exact lt_of_le_of_lt (le_abs_self (x - y)) (by simpa [abs_sub_comm] using hydist)
        linarith
      have hy_right_lt : y < P.pts (i + 1) := by
        have hyx : y - x < r := by
          exact lt_of_le_of_lt (le_abs_self (y - x)) hydist
        linarith
      exact ⟨le_of_lt hy_left_lt, le_of_lt hy_right_lt⟩
    · have hnot_internal : ¬ i + 1 < P.n := by
        intro hnext
        exact hxnotB (by
          rw [hxright]
          exact hInternal (i + 1) (Nat.succ_pos i) hnext)
      have hlast : i + 1 = P.n := by
        exact le_antisymm (Nat.succ_le_of_lt hi) (le_of_not_gt hnot_internal)
      have hright_end : P.pts (i + 1) = b := by
        rw [hlast, P.pts_end]
      let r : ℝ := (x - P.pts i) / 2
      have hleftgap : 0 < x - P.pts i := sub_pos.mpr hxcell.1
      have hr : 0 < r := by
        dsimp [r]
        exact half_pos hleftgap
      refine ⟨x, r, hxLarge, hr, ?_⟩
      intro y hyI hydist
      have hr_le_left : r ≤ x - P.pts i := by
        dsimp [r]
        exact half_le_self (le_of_lt hleftgap)
      have hy_left_lt : P.pts i < y := by
        have hxy : x - y < r := by
          exact lt_of_le_of_lt (le_abs_self (x - y)) (by simpa [abs_sub_comm] using hydist)
        linarith
      have hy_right : y ≤ P.pts (i + 1) := by
        rw [hright_end]
        exact hyI.2
      exact ⟨le_of_lt hy_left_lt, hy_right⟩

theorem prob_7_3_exists_compact_subset_largeOscillationSet_pos
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ} (n : ℕ)
    (hpos :
      0 < (((F.measure.restrict (Icc a b))
        (prob_7_3_largeOscillationSet f a b n)).toReal)) :
    ∃ K : Set ℝ,
      IsCompact K ∧
      K ⊆ prob_7_3_largeOscillationSet f a b n ∧
      0 < (((F.measure.restrict (Icc a b)) K).toReal) := by
  let μr : Measure ℝ := F.measure.restrict (Icc a b)
  letI : IsFiniteMeasure μr :=
    prob_7_3_isFiniteMeasure_restrict_Icc (a := a) (b := b) F
  have hmeas :
      MeasurableSet (prob_7_3_largeOscillationSet f a b n) :=
    prob_7_3_measurableSet_largeOscillationSet (a := a) (b := b) (f := f) n
  have hposENN :
      (0 : ENNReal) < μr (prob_7_3_largeOscillationSet f a b n) := by
    simpa [μr] using (ENNReal.toReal_pos_iff.mp hpos).1
  rcases hmeas.exists_lt_isCompact (μ := μr) hposENN with
    ⟨K, hKsub, hKcompact, hKposENN⟩
  refine ⟨K, hKcompact, hKsub, ?_⟩
  have hK_ne_zero : μr K ≠ 0 := ne_of_gt hKposENN
  have hK_ne_top : μr K ≠ ⊤ := measure_ne_top μr K
  simpa [μr] using ENNReal.toReal_pos hK_ne_zero hK_ne_top

theorem prob_7_3_exists_compact_subset_largeOscillationSet_off_left_pos
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ} (n : ℕ)
    (hAtom : F.measure {a} = 0)
    (hpos :
      0 < (((F.measure.restrict (Icc a b))
        (prob_7_3_largeOscillationSet f a b n)).toReal)) :
    ∃ K : Set ℝ,
      IsCompact K ∧
      K ⊆ prob_7_3_largeOscillationSet f a b n ∧
      a ∉ K ∧
      0 < (((F.measure.restrict (Icc a b)) K).toReal) := by
  let A : Set ℝ := prob_7_3_largeOscillationSet f a b n
  let μr : Measure ℝ := F.measure.restrict (Icc a b)
  letI : IsFiniteMeasure μr :=
    prob_7_3_isFiniteMeasure_restrict_Icc (a := a) (b := b) F
  have hmeasA : MeasurableSet A :=
    prob_7_3_measurableSet_largeOscillationSet (a := a) (b := b) (f := f) n
  have hmeas : MeasurableSet (A \ {a}) := hmeasA.diff (measurableSet_singleton a)
  have hposDiff :
      0 < (μr (A \ {a})).toReal := by
    have hAtomRestrict : μr {a} = 0 := by
      simpa [μr] using prob_7_3_endpoint_atom_convention_support
        (a := a) (b := b) F hAtom
    rw [measure_diff_null hAtomRestrict]
    simpa [A, μr] using hpos
  have hposENN : (0 : ENNReal) < μr (A \ {a}) := by
    exact (ENNReal.toReal_pos_iff.mp hposDiff).1
  rcases hmeas.exists_lt_isCompact (μ := μr) hposENN with
    ⟨K, hKsubDiff, hKcompact, hKposENN⟩
  refine ⟨K, hKcompact, ?_, ?_, ?_⟩
  · intro x hx
    exact (hKsubDiff hx).1
  · intro haK
    exact (hKsubDiff haK).2 rfl
  · have hK_ne_zero : μr K ≠ 0 := ne_of_gt hKposENN
    have hK_ne_top : μr K ≠ ⊤ := measure_ne_top μr K
    simpa [μr] using ENNReal.toReal_pos hK_ne_zero hK_ne_top
