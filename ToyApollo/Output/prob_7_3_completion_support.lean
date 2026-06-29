/-
TASK ID: prob_7_3_completion_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_7_3_forward_support

open MeasureTheory Set Filter

noncomputable section

theorem prob_7_3_null_closed_layer_has_small_open_neighborhood
    (F : StieltjesFunction ℝ) {a b : ℝ} {D : Set ℝ}
    (_hDclosed : IsClosed D)
    (_hDsub : D ⊆ Icc a b)
    (hDnull : (F.measure.restrict (Icc a b)) D = 0)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ G : Set ℝ,
      IsOpen G ∧ D ⊆ G ∧
      (((F.measure.restrict (Icc a b)) G).toReal) < τ := by
  let μ : Measure ℝ := F.measure.restrict (Icc a b)
  have hlt : μ D < ENNReal.ofReal τ := by
    rw [hDnull]
    exact ENNReal.ofReal_pos.mpr hτ
  rcases Set.exists_isOpen_lt_of_lt (μ := μ) D (ENNReal.ofReal τ) hlt with
    ⟨G, hDG, hGopen, hGmeasure⟩
  refine ⟨G, hGopen, hDG, ?_⟩
  have hG_ne_top : μ G ≠ ⊤ := (lt_of_lt_of_le hGmeasure le_top).ne
  have hτ_ne_top : ENNReal.ofReal τ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hto :
      (μ G).toReal < (ENNReal.ofReal τ).toReal :=
    (ENNReal.toReal_lt_toReal hG_ne_top hτ_ne_top).2 hGmeasure
  simpa [μ, ENNReal.toReal_ofReal (le_of_lt hτ)] using hto

theorem prob_7_3_cell_oscillation_le_of_pairwise_small_on_subinterval
    {a b eta : ℝ} {f : ℝ → ℝ} (P : DarbouxRS.Partition a b) {i : ℕ}
    (hi : i < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hsmall :
      ∀ y : ℝ, y ∈ DarbouxRS.subinterval P i →
        ∀ z : ℝ, z ∈ DarbouxRS.subinterval P i → |f y - f z| < eta) :
    DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i ≤ eta := by
  exact
    Thm11SourceRoute.upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
      (P := P) (i := i) hi hAbove hBelow
      (fun y hy z hz => le_of_lt (hsmall y hy z hz))

theorem prob_7_3_same_subinterval_abs_sub_le_mesh
    {a b : ℝ} (P : DarbouxRS.Partition a b) {i : ℕ} (hi : i < P.n)
    {y z : ℝ}
    (hy : y ∈ DarbouxRS.subinterval P i)
    (hz : z ∈ DarbouxRS.subinterval P i) :
    |y - z| ≤ P.mesh := by
  have hlen : P.pts (i + 1) - P.pts i ≤ P.mesh := by
    unfold DarbouxRS.Partition.mesh
    exact Finset.le_sup' (s := Finset.range P.n)
      (f := fun j => P.pts (j + 1) - P.pts j) (Finset.mem_range.mpr hi)
  have habs : |y - z| ≤ P.pts (i + 1) - P.pts i := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [hy.1, hz.2]
    · nlinarith [hy.2, hz.1]
  exact le_trans habs hlen

theorem prob_7_3_compact_complement_uniform_small_oscillation
    {a b eta : ℝ} {f : ℝ → ℝ} (n : ℕ) {G : Set ℝ}
    (heta : 0 < eta)
    (heta_def : eta = (1 : ℝ) / ((n : ℝ) + 1))
    (hGopen : IsOpen G)
    (hLayerSubG : prob_7_3_largeOscillationSet f a b n ⊆ G) :
    ∃ lambda : ℝ, 0 < lambda ∧
      ∀ P : DarbouxRS.Partition a b, ∀ i : ℕ, i < P.n →
        P.mesh < lambda →
        (DarbouxRS.subinterval P i ∩ (Icc a b \ G)).Nonempty →
        ∀ y : ℝ, y ∈ DarbouxRS.subinterval P i →
          ∀ z : ℝ, z ∈ DarbouxRS.subinterval P i → |f y - f z| < eta := by
  classical
  let K : Set ℝ := Icc a b \ G
  have hKcompact : IsCompact K := isCompact_Icc.diff hGopen
  have hlocal :
      ∀ x : ℝ, x ∈ K →
        ∃ delta : ℝ, 0 < delta ∧
          ∀ y : ℝ, y ∈ Icc a b → |y - x| < delta →
            ∀ z : ℝ, z ∈ Icc a b → |z - x| < delta →
              |f y - f z| < eta := by
    intro x hxK
    have hxI : x ∈ Icc a b := hxK.1
    have hxNotLayer : x ∉ prob_7_3_largeOscillationSet f a b n := by
      intro hxLayer
      exact hxK.2 (hLayerSubG hxLayer)
    have hxNotOsc :
        ¬ prob_7_3_relativeLocalOscillationAtLeast f a b x eta := by
      intro hosc
      have hosc' :
          prob_7_3_relativeLocalOscillationAtLeast f a b x
            ((1 : ℝ) / ((n : ℝ) + 1)) := by
        simpa [← heta_def] using hosc
      exact hxNotLayer (by
        simpa [prob_7_3_largeOscillationSet] using hosc')
    by_contra hno
    push_neg at hno
    exact hxNotOsc ⟨hxI, heta, hno⟩
  let r : ℝ → ℝ := fun x =>
    if hx : x ∈ K then Classical.choose (hlocal x hx) / 4 else 1
  have hr_pos : ∀ x : ℝ, x ∈ K → 0 < r x := by
    intro x hxK
    have hdelta_pos : 0 < Classical.choose (hlocal x hxK) :=
      (Classical.choose_spec (hlocal x hxK)).1
    dsimp [r]
    rw [dif_pos hxK]
    linarith
  by_cases hKnonempty : K.Nonempty
  · rcases prob_7_3_compact_finite_ball_subcover hKcompact r hr_pos with
      ⟨S, hSsubK, hKcover⟩
    have hSnonempty : S.Nonempty := by
      rcases hKnonempty with ⟨x0, hx0K⟩
      have hx0cover := hKcover hx0K
      rcases mem_iUnion.mp hx0cover with ⟨c, hcCover⟩
      rcases mem_iUnion.mp hcCover with ⟨hcS, _hball⟩
      exact ⟨c, hcS⟩
    let lambda : ℝ := S.inf' hSnonempty r
    have hlambda_pos : 0 < lambda := by
      have hmem :
          S.inf' hSnonempty r ∈ Ioi (0 : ℝ) := by
        refine Finset.inf'_mem
          (s := Ioi (0 : ℝ))
          (w := ?_) (t := S) hSnonempty (p := r) ?_
        · intro x hx y hy
          have hx' : 0 < x := by simpa using hx
          have hy' : 0 < y := by simpa using hy
          change 0 < min x y
          exact lt_min hx' hy'
        · intro x hxS
          exact hr_pos x (hSsubK x hxS)
      simpa [lambda] using hmem
    refine ⟨lambda, hlambda_pos, ?_⟩
    intro P i hi hmesh hmeet y hy z hz
    rcases hmeet with ⟨u, huCell, huK⟩
    have huCover := hKcover huK
    rcases mem_iUnion.mp huCover with ⟨c, hcCover⟩
    rcases mem_iUnion.mp hcCover with ⟨hcS, huBall⟩
    have hcK : c ∈ K := hSsubK c hcS
    have hlambda_le_rc : lambda ≤ r c := by
      exact Finset.inf'_le (f := r) hcS
    have hmesh_lt_rc : P.mesh < r c := lt_of_lt_of_le hmesh hlambda_le_rc
    let delta : ℝ := Classical.choose (hlocal c hcK)
    have hdelta_spec := Classical.choose_spec (hlocal c hcK)
    have hdelta_pos : 0 < delta := hdelta_spec.1
    have hosc := hdelta_spec.2
    have hrc : r c = delta / 4 := by
      dsimp [r, delta]
      rw [dif_pos hcK]
    have hmesh_delta : P.mesh < delta / 4 := by
      simpa [hrc] using hmesh_lt_rc
    have huc_delta : |u - c| < delta / 4 := by
      simpa [Metric.mem_ball, Real.dist_eq, hrc] using huBall
    have hyu : |y - u| ≤ P.mesh :=
      prob_7_3_same_subinterval_abs_sub_le_mesh P hi hy huCell
    have hzu : |z - u| ≤ P.mesh :=
      prob_7_3_same_subinterval_abs_sub_le_mesh P hi hz huCell
    have hyc : |y - c| < delta := by
      have htri : |y - c| ≤ |y - u| + |u - c| := by
        calc
          |y - c| = |(y - u) + (u - c)| := by ring_nf
          _ ≤ |y - u| + |u - c| := abs_add_le _ _
      have hsum : |y - u| + |u - c| < delta / 4 + delta / 4 :=
        add_lt_add_of_le_of_lt (le_of_lt (lt_of_le_of_lt hyu hmesh_delta)) huc_delta
      exact lt_of_le_of_lt htri (lt_trans hsum (by linarith))
    have hzc : |z - c| < delta := by
      have htri : |z - c| ≤ |z - u| + |u - c| := by
        calc
          |z - c| = |(z - u) + (u - c)| := by ring_nf
          _ ≤ |z - u| + |u - c| := abs_add_le _ _
      have hsum : |z - u| + |u - c| < delta / 4 + delta / 4 :=
        add_lt_add_of_le_of_lt (le_of_lt (lt_of_le_of_lt hzu hmesh_delta)) huc_delta
      exact lt_of_le_of_lt htri (lt_trans hsum (by linarith))
    have hyI : y ∈ Icc a b := DarbouxRS.subinterval_subset_Icc_core P hi hy
    have hzI : z ∈ Icc a b := DarbouxRS.subinterval_subset_Icc_core P hi hz
    exact hosc y hyI hyc z hzI hzc
  · refine ⟨1, zero_lt_one, ?_⟩
    intro P i hi hmesh hmeet y hy z hz
    rcases hmeet with ⟨u, _huCell, huK⟩
    exact (hKnonempty ⟨u, huK⟩).elim

theorem prob_7_3_partitionOscillation_bound_of_good_bad_cells
    (F : StieltjesFunction ℝ) {a b eta C : ℝ} {f : ℝ → ℝ}
    (P : DarbouxRS.Partition a b) (G : Set ℝ)
    (hab : a < b)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hCbound : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C)
    (hCnonneg : 0 ≤ C)
    (heta_nonneg : 0 ≤ eta)
    (hGood : ∀ i : ℕ, i < P.n →
      (DarbouxRS.subinterval P i ∩ (Icc a b \ G)).Nonempty →
      DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i ≤ eta) :
    Thm11SourceRoute.partitionOscillation P f F ≤
      eta * (F b - F a) +
        (2 * C) * (((F.measure.restrict (Icc a b)) G).toReal) := by
  classical
  let K : Set ℝ := Icc a b \ G
  let B : Finset ℕ :=
    (Finset.range P.n).filter
      (fun i : ℕ => ¬ (DarbouxRS.subinterval P i ∩ K).Nonempty)
  have hs : DarbouxRS.SourceHypotheses a b f F :=
    ⟨hab, hAbove, hBelow, F.mono.monotoneOn (Icc a b)⟩
  have hgood_split :
      ∀ i : ℕ, i < P.n → i ∉ B →
        DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i ≤ eta := by
    intro i hi hiNotB
    have hmeet : (DarbouxRS.subinterval P i ∩ K).Nonempty := by
      by_contra hnot
      exact hiNotB (by simp [B, hi, hnot])
    exact hGood i hi hmeet
  have hbad_split :
      ∀ i : ℕ, i < P.n → i ∈ B →
        DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i ≤ 2 * C := by
    intro i hi _hiB
    exact Thm11SourceRoute.upperStep_sub_lowerStep_le_two_mul_abs_bound
      P hi hAbove hBelow hCbound
  have hsplit := Thm11SourceRoute.partitionOscillation_le_good_bad_split
    (f := f) (α := F) (a := a) (b := b) (C := C) (eta := eta)
    hs P B heta_nonneg hgood_split hbad_split
  have hfilter_eq :
      (Finset.range P.n).filter (fun i : ℕ => i ∈ B) = B := by
    ext i
    simp [B]
  have hsplit' :
      Thm11SourceRoute.partitionOscillation P f F ≤
        eta * (F b - F a) +
          2 * C *
            (∑ i ∈ B, (F (P.pts (i + 1)) - F (P.pts i))) := by
    simpa [hfilter_eq] using hsplit
  have hBsub : ∀ i ∈ B, i < P.n := by
    intro i hiB
    exact Finset.mem_range.mp ((Finset.mem_filter.mp hiB).1)
  have hBcellSub : ∀ i ∈ B, Ioc (P.pts i) (P.pts (i + 1)) ⊆ G := by
    intro i hiB x hxcell
    have hi : i < P.n := hBsub i hiB
    have hbad : ¬ (DarbouxRS.subinterval P i ∩ K).Nonempty :=
      (Finset.mem_filter.mp hiB).2
    have hxClosed : x ∈ DarbouxRS.subinterval P i :=
      ⟨le_of_lt hxcell.1, hxcell.2⟩
    have hxI : x ∈ Icc a b := DarbouxRS.subinterval_subset_Icc_core P hi hxClosed
    by_contra hxG
    exact hbad ⟨x, hxClosed, hxI, hxG⟩
  have hbadSumLe :
      (∑ i ∈ B, (F (P.pts (i + 1)) - F (P.pts i))) ≤
        (((F.measure.restrict (Icc a b)) G).toReal) := by
    exact prob_7_3_partition_cell_increment_sum_le_open_measure_toReal
      (F := F) (P := P) (S := B) hBsub hBcellSub
  have hcoef_nonneg : 0 ≤ 2 * C := by nlinarith
  have hbadTermLe :
      2 * C * (∑ i ∈ B, (F (P.pts (i + 1)) - F (P.pts i))) ≤
        2 * C * (((F.measure.restrict (Icc a b)) G).toReal) :=
    mul_le_mul_of_nonneg_left hbadSumLe hcoef_nonneg
  linarith

theorem prob_7_3_largeOscillationSet_nulls_imply_darbouxGapSmall
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b)
    (hBounded : ∃ M, ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ M)
    (hNull : ∀ n : ℕ,
      (F.measure.restrict (Icc a b)) (prob_7_3_largeOscillationSet f a b n) = 0) :
    Thm11SourceRoute.ClosedIntervalDarbouxGapSmall a b f F := by
  intro eps heps
  rcases hBounded with ⟨M, hM⟩
  let C : ℝ := max M 0 + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [le_max_right M 0]
  have hCnonneg : 0 ≤ C := le_of_lt hCpos
  have hCbound : ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C := by
    intro x hx
    exact le_trans (hM x hx) (by
      dsimp [C]
      linarith [le_max_left M 0])
  have hBoundedC : ∃ C' : ℝ, ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C' :=
    ⟨C, hCbound⟩
  rcases prob_7_3_bddAbove_bddBelow_of_abs_bound
      (a := a) (b := b) (f := f) hBoundedC with
    ⟨hAbove, hBelow⟩
  let span : ℝ := F b - F a
  have hspan_nonneg : 0 ≤ span := by
    dsimp [span]
    exact sub_nonneg.mpr (F.mono (le_of_lt hab))
  have hspan_plus_pos : 0 < span + 1 := by linarith
  let quota : ℝ := eps / (2 * (span + 1))
  have hquota_pos : 0 < quota := by
    dsimp [quota]
    positivity
  rcases exists_nat_one_div_lt hquota_pos with ⟨n, hnsmall⟩
  let eta : ℝ := (1 : ℝ) / ((n : ℝ) + 1)
  have heta_pos : 0 < eta := by
    dsimp [eta]
    positivity
  have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
  have heta_def : eta = (1 : ℝ) / ((n : ℝ) + 1) := rfl
  have heta_span_lt : eta * span < eps / 2 := by
    have hspan_le : span ≤ span + 1 := by linarith
    have heta_span_le : eta * span ≤ eta * (span + 1) :=
      mul_le_mul_of_nonneg_left hspan_le heta_nonneg
    have heta_span_plus_lt : eta * (span + 1) < quota * (span + 1) :=
      mul_lt_mul_of_pos_right hnsmall hspan_plus_pos
    have hquota_mul : quota * (span + 1) = eps / 2 := by
      dsimp [quota]
      field_simp [ne_of_gt hspan_plus_pos]
    nlinarith
  let tau : ℝ := eps / (4 * C)
  have htau_pos : 0 < tau := by
    dsimp [tau]
    positivity
  let D : Set ℝ := prob_7_3_largeOscillationSet f a b n
  have hDclosed : IsClosed D := by
    dsimp [D]
    exact prob_7_3_isClosed_largeOscillationSet (a := a) (b := b) (f := f) n
  have hDsub : D ⊆ Icc a b := by
    intro x hx
    exact hx.1
  have hDnull : (F.measure.restrict (Icc a b)) D = 0 := by
    dsimp [D]
    exact hNull n
  rcases prob_7_3_null_closed_layer_has_small_open_neighborhood
      (F := F) (a := a) (b := b) (D := D)
      hDclosed hDsub hDnull htau_pos with
    ⟨G, hGopen, hDsubG, hGsmall⟩
  have hbad_lt :
      (2 * C) * (((F.measure.restrict (Icc a b)) G).toReal) < eps / 2 := by
    have hcoef_pos : 0 < 2 * C := by positivity
    have hmul := mul_lt_mul_of_pos_left hGsmall hcoef_pos
    have hcalc : (2 * C) * tau = eps / 2 := by
      dsimp [tau]
      field_simp [ne_of_gt hCpos]
      ring
    nlinarith
  rcases prob_7_3_compact_complement_uniform_small_oscillation
      (a := a) (b := b) (f := f) (n := n) (eta := eta) (G := G)
      heta_pos heta_def hGopen (by simpa [D] using hDsubG) with
    ⟨delta, hdelta_pos, Hdelta⟩
  refine ⟨delta, hdelta_pos, ?_⟩
  intro P hmesh
  have hGood : ∀ i : ℕ, i < P.n →
      (DarbouxRS.subinterval P i ∩ (Icc a b \ G)).Nonempty →
      DarbouxRS.upperStep P f i - DarbouxRS.lowerStep P f i ≤ eta := by
    intro i hi hmeet
    exact prob_7_3_cell_oscillation_le_of_pairwise_small_on_subinterval
      (P := P) (i := i) hi hAbove hBelow
      (Hdelta P i hi hmesh hmeet)
  have hosc_bound :
      Thm11SourceRoute.partitionOscillation P f F ≤
        eta * (F b - F a) +
          (2 * C) * (((F.measure.restrict (Icc a b)) G).toReal) := by
    exact prob_7_3_partitionOscillation_bound_of_good_bad_cells
      (F := F) (P := P) (G := G) hab hAbove hBelow hCbound hCnonneg
      heta_nonneg hGood
  have hosc_lt : Thm11SourceRoute.partitionOscillation P f F < eps := by
    have hsum_lt :
        eta * (F b - F a) +
            (2 * C) * (((F.measure.restrict (Icc a b)) G).toReal) < eps := by
      dsimp [span] at heta_span_lt
      linarith
    exact lt_of_le_of_lt hosc_bound hsum_lt
  simpa [Thm11SourceRoute.upperSum_sub_lowerSum_eq_partitionOscillation] using hosc_lt

theorem prob_7_3_ae_continuity_implies_rsIntegrable
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b)
    (hBounded : ∃ M, ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ M)
    (hcont : ∀ᵐ x ∂(F.measure.restrict (Icc a b)),
      ContinuousWithinAt f (Icc a b) x) :
    RSIntegrable f F a b := by
  have hNull : ∀ n : ℕ,
      (F.measure.restrict (Icc a b)) (prob_7_3_largeOscillationSet f a b n) = 0 :=
    prob_7_3_ae_continuity_implies_largeOscillationSet_nulls
      (μ := F.measure) (a := a) (b := b) (f := f) hcont
  exact prob_7_3_rsIntegrable_of_darbouxGapSmall
    (a := a) (b := b) (f := f) (α := (F : ℝ → ℝ)) hab F.mono hBounded
    (prob_7_3_largeOscillationSet_nulls_imply_darbouxGapSmall
      (F := F) (a := a) (b := b) (f := f) hab hBounded hNull)

theorem prob_7_3_partA_rsIntegrable_iff_ae_continuous
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b)
    (hAtom : F.measure {a} = 0)
    (hBounded : ∃ M, ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ M) :
    RSIntegrable f F a b ↔
      ∀ᵐ x ∂(F.measure.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x := by
  constructor
  · intro hRS
    exact prob_7_3_rsIntegrable_implies_ae_continuity
      (F := F) (a := a) (b := b) (f := f) hab hAtom hBounded hRS
  · intro hcont
    exact prob_7_3_ae_continuity_implies_rsIntegrable
      (F := F) (a := a) (b := b) (f := f) hab hBounded hcont

theorem prob_7_3_integral_Icc_eq_rsIntegral
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b)
    (hAtom : F.measure {a} = 0)
    (hBounded : ∃ M, ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ M)
    (hRS : RSIntegrable f F a b) :
    IntegrableOn f (Icc a b) F.measure ∧
      ∫ x in Icc a b, f x ∂F.measure = rsIntegral f F a b hRS := by
  have hcont :
      ∀ᵐ x ∂(F.measure.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x :=
    (prob_7_3_partA_rsIntegrable_iff_ae_continuous
      (F := F) (a := a) (b := b) (f := f) hab hAtom hBounded).1 hRS
  have hIcc : IntegrableOn f (Icc a b) F.measure :=
    prob_7_3_integrableOn_Icc_of_ae_continuous_bounded
      (F := F) (a := a) (b := b) (f := f) hBounded hcont
  have hIoc : IntegrableOn f (Ioc a b) F.measure :=
    hIcc.mono_set Ioc_subset_Icc_self
  have hBounds := prob_7_3_bddAbove_bddBelow_of_abs_bound
    (a := a) (b := b) (f := f) hBounded
  have hIocEq :
      ∫ x in Ioc a b, f x ∂F.measure = rsIntegral f F a b hRS :=
    prob_7_3_ioc_integral_eq_rsIntegral_of_integrableOn
      (F := F) (a := a) (b := b) (f := f) hIoc hBounds.1 hBounds.2 hRS
  have hEndpoint :
      ∫ x in Icc a b, f x ∂F.measure =
        (F.measure {a}).toReal * f a + ∫ x in Ioc a b, f x ∂F.measure :=
    thm_7_9_integral_Icc_eq_singleton_add_Ioc F (le_of_lt hab) hIcc
  refine ⟨hIcc, ?_⟩
  calc
    ∫ x in Icc a b, f x ∂F.measure
        = ∫ x in Ioc a b, f x ∂F.measure := by
          simpa [hAtom] using hEndpoint
    _ = rsIntegral f F a b hRS := hIocEq

theorem prob_7_3_integrableOn_completion_of_integrableOn
    (μ : Measure ℝ) {s : Set ℝ} {f : ℝ → ℝ}
    (hs : MeasurableSet s) (h : IntegrableOn f s μ) :
    IntegrableOn (fun x : NullMeasurableSpace ℝ μ => f x) s μ.completion := by
  rw [IntegrableOn] at h ⊢
  have hm : (inferInstance : MeasurableSpace ℝ) ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ μ)) := by
    intro t ht
    exact ht.nullMeasurableSet
  have hμtrim : μ.completion.trim hm = μ := by
    refine @Measure.ext (NullMeasurableSpace ℝ μ)
      (inferInstance : MeasurableSpace ℝ) _ _ ?_
    intro t ht
    rw [@trim_measurableSet_eq (NullMeasurableSpace ℝ μ)
      (inferInstance : MeasurableSpace ℝ)
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ μ))
      μ.completion t hm ht]
    rw [Measure.completion_apply]
    rfl
  have hrestrict_trim :
      @Measure.restrict (NullMeasurableSpace ℝ μ)
          (inferInstance : MeasurableSpace ℝ) (μ.completion.trim hm) s =
        (μ.completion.restrict s).trim hm := by
    exact @restrict_trim (NullMeasurableSpace ℝ μ)
      (inferInstance : MeasurableSpace ℝ)
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ μ))
      s hm μ.completion hs
  have htrim : (μ.completion.restrict s).trim hm = μ.restrict s := by
    rw [← hrestrict_trim, hμtrim]
    rfl
  exact integrable_of_integrable_trim hm (by rwa [htrim])

theorem prob_7_3_setIntegral_completion_eq
    (μ : Measure ℝ) {s : Set ℝ} {f : ℝ → ℝ}
    (hs : MeasurableSet s) (h : IntegrableOn f s μ) :
    ∫ x in s, (fun x : NullMeasurableSpace ℝ μ => f x) x ∂μ.completion =
      ∫ x in s, f x ∂μ := by
  rw [IntegrableOn] at h
  have hm : (inferInstance : MeasurableSpace ℝ) ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ μ)) := by
    intro t ht
    exact ht.nullMeasurableSet
  have hμtrim : μ.completion.trim hm = μ := by
    refine @Measure.ext (NullMeasurableSpace ℝ μ)
      (inferInstance : MeasurableSpace ℝ) _ _ ?_
    intro t ht
    rw [@trim_measurableSet_eq (NullMeasurableSpace ℝ μ)
      (inferInstance : MeasurableSpace ℝ)
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ μ))
      μ.completion t hm ht]
    rw [Measure.completion_apply]
    rfl
  have hrestrict_trim :
      @Measure.restrict (NullMeasurableSpace ℝ μ)
          (inferInstance : MeasurableSpace ℝ) (μ.completion.trim hm) s =
        (μ.completion.restrict s).trim hm := by
    exact @restrict_trim (NullMeasurableSpace ℝ μ)
      (inferInstance : MeasurableSpace ℝ)
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ μ))
      s hm μ.completion hs
  have htrim : (μ.completion.restrict s).trim hm = μ.restrict s := by
    rw [← hrestrict_trim, hμtrim]
    rfl
  have hf_aes : @AEStronglyMeasurable (NullMeasurableSpace ℝ μ) ℝ
      _ (inferInstance : MeasurableSpace ℝ)
      (inferInstance : MeasurableSpace ℝ)
      (fun x : NullMeasurableSpace ℝ μ => f x)
      ((μ.completion.restrict s).trim hm) := by
    simpa [htrim] using h.aestronglyMeasurable
  have hEqWhole :
      ∫ x, (fun x : NullMeasurableSpace ℝ μ => f x) x ∂(μ.completion.restrict s) =
        ∫ x, (fun x : NullMeasurableSpace ℝ μ => f x) x
          ∂((μ.completion.restrict s).trim hm) := by
    exact @integral_trim_ae ℝ _ _ (NullMeasurableSpace ℝ μ)
      (inferInstance : MeasurableSpace ℝ)
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ μ))
      (μ.completion.restrict s) hm
      (f := fun x : NullMeasurableSpace ℝ μ => f x) hf_aes
  simpa [htrim] using hEqWhole

theorem prob_7_3_partB_completion_integrable_integral_eq
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b)
    (hAtom : F.measure {a} = 0)
    (hBounded : ∃ M, ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ M)
    (hRS : RSIntegrable f F a b) :
    IntegrableOn (fun x : NullMeasurableSpace ℝ F.measure => f x)
        (Icc a b) F.measure.completion ∧
      rsIntegral f F a b hRS =
        ∫ x in Icc a b,
          (fun x : NullMeasurableSpace ℝ F.measure => f x) x
            ∂F.measure.completion := by
  have hOrd := prob_7_3_integral_Icc_eq_rsIntegral
    (F := F) (a := a) (b := b) (f := f) hab hAtom hBounded hRS
  have hCompInt :
      IntegrableOn (fun x : NullMeasurableSpace ℝ F.measure => f x)
        (Icc a b) F.measure.completion :=
    prob_7_3_integrableOn_completion_of_integrableOn
      (μ := F.measure) (s := Icc a b) (f := f) measurableSet_Icc hOrd.1
  have hCompEq :
      ∫ x in Icc a b,
          (fun x : NullMeasurableSpace ℝ F.measure => f x) x
            ∂F.measure.completion =
        ∫ x in Icc a b, f x ∂F.measure :=
    prob_7_3_setIntegral_completion_eq
      (μ := F.measure) (s := Icc a b) (f := f) measurableSet_Icc hOrd.1
  refine ⟨hCompInt, ?_⟩
  calc
    rsIntegral f F a b hRS
        = ∫ x in Icc a b, f x ∂F.measure := hOrd.2.symm
    _ = ∫ x in Icc a b,
          (fun x : NullMeasurableSpace ℝ F.measure => f x) x
            ∂F.measure.completion := hCompEq.symm

theorem prob_7_3_support_result
    {a b : ℝ} {f : ℝ → ℝ} {α : StieltjesFunction ℝ}
    (hab : a < b)
    (hBounded : ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M)
    (hAtom : α.measure {a} = 0) :
    (RSIntegrable f α a b ↔
      ∀ᵐ x ∂(α.measure.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x) ∧
    (∀ hRS : RSIntegrable f α a b,
      IntegrableOn (fun x : NullMeasurableSpace ℝ α.measure => f x) (Icc a b)
          α.measure.completion ∧
        rsIntegral f α a b hRS =
          ∫ x in Icc a b, (fun x : NullMeasurableSpace ℝ α.measure => f x) x
            ∂α.measure.completion) := by
  constructor
  · exact prob_7_3_partA_rsIntegrable_iff_ae_continuous
      (F := α) (a := a) (b := b) (f := f) hab hAtom hBounded
  · intro hRS
    exact prob_7_3_partB_completion_integrable_integral_eq
      (F := α) (a := a) (b := b) (f := f) hab hAtom hBounded hRS
