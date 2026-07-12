/-
TASK ID: thm_1_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_1_2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set MeasureTheory DarbouxRS
open scoped BigOperators Pointwise Interval

noncomputable section

namespace Thm_1_4

lemma strict_interval_of_rsIntegrable {f α : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f α a b) :
    a < b := by
  rcases h with ⟨_L, hL⟩
  exact hL.1.1

lemma taggedSum_between_lower_upper {f α : ℝ → ℝ} {a b : ℝ}
    (hs : SourceHypotheses a b f α)
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags) :
    lowerSum P f α ≤ taggedSum P tags f α ∧
      taggedSum P tags f α ≤ upperSum P f α := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  constructor
  · unfold lowerSum taggedSum
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hcellBelow : BddBelow (f '' Partition.subinterval P i) :=
      BddBelow.mono
        (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
        hBelow
    have hlow_le_tag : lowerStep P f i ≤ f (tags i) := by
      unfold lowerStep
      exact csInf_le hcellBelow ⟨tags i, htags i, rfl⟩
    have hinc_nonneg :
        0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩
    exact mul_le_mul_of_nonneg_right hlow_le_tag hinc_nonneg
  · unfold taggedSum upperSum
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hcellAbove : BddAbove (f '' Partition.subinterval P i) :=
      BddAbove.mono
        (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
        hAbove
    have htag_le_up : f (tags i) ≤ upperStep P f i := by
      unfold upperStep
      exact le_csSup hcellAbove ⟨tags i, htags i, rfl⟩
    have hinc_nonneg :
        0 ≤ α (P.pts i.succ) - α (P.pts i.castSucc) :=
      DarbouxRS.partition_increment_nonneg_of_source_core P
        ⟨hab, hAbove, hBelow, hmono⟩
    exact mul_le_mul_of_nonneg_right htag_le_up hinc_nonneg

theorem taggedCommonLimit_of_upperLowerCommonLimit {f α : ℝ → ℝ} {a b L : ℝ}
    (hUL : rsUpperLowerCommonLimit a b f α L) :
    rsTaggedCommonLimit a b f α L := by
  rcases hUL with ⟨hs, hlim⟩
  refine ⟨hs, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨δ, hδ, Hδ⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := Hδ P hmesh
  have hbetween := taggedSum_between_lower_upper hs P tags htags
  have hlower_abs := abs_lt.mp hP.2
  have hupper_abs := abs_lt.mp hP.1
  refine abs_lt.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

noncomputable def partitionOscillation {a b : ℝ}
    (P : Partition a b) (f α : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    (upperStep P f i - lowerStep P f i) *
      (α (P.pts i.succ) - α (P.pts i.castSucc))

lemma upperSum_sub_lowerSum_eq_partitionOscillation {f α : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) :
    upperSum P f α - lowerSum P f α =
      partitionOscillation P f α := by
  unfold partitionOscillation upperSum lowerSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

lemma exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow {f : ℝ → ℝ} {a b : ℝ}
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ C := by
  rcases hAbove with ⟨U, hU⟩
  rcases hBelow with ⟨L, hL⟩
  refine ⟨max |U| |L| + 1, ?_, ?_⟩
  · positivity
  · intro x hx
    have hxU : f x ≤ U := hU ⟨x, hx, rfl⟩
    have hxL : L ≤ f x := hL ⟨x, hx, rfl⟩
    refine abs_le.mpr ⟨?_, ?_⟩
    · have hL_abs : -|L| ≤ L := neg_abs_le L
      have hC_abs : |L| ≤ max |U| |L| + 1 := by
        calc
          |L| ≤ max |U| |L| := le_max_right _ _
          _ ≤ max |U| |L| + 1 := by linarith
      linarith
    · have hU_abs : U ≤ |U| := le_abs_self U
      have hC_abs : |U| ≤ max |U| |L| + 1 := by
        calc
          |U| ≤ max |U| |L| := le_max_left _ _
          _ ≤ max |U| |L| + 1 := by linarith
      linarith

lemma upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
    {f : ℝ → ℝ} {a b eta : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hosc :
      ∀ x, x ∈ Partition.subinterval P i →
      ∀ y, y ∈ Partition.subinterval P i → |f x - f y| ≤ eta) :
    upperStep P f i - lowerStep P f i ≤ eta := by
  let cell := Partition.subinterval P i
  have hcell_nonempty : (f '' cell).Nonempty := by
    refine ⟨f (P.pts i.castSucc), ?_⟩
    refine ⟨P.pts i.castSucc, ?_, rfl⟩
    exact ⟨le_rfl, le_of_lt (P.strict_mono Fin.castSucc_lt_succ)⟩
  have hcellAbove : BddAbove (f '' cell) :=
    BddAbove.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
      hAbove
  have hcellBelow : BddBelow (f '' cell) :=
    BddBelow.mono
      (Set.image_mono (DarbouxRS.subinterval_subset_Icc_core P (i := i)))
      hBelow
  have hsup_le :
      sSup (f '' cell) ≤ sInf (f '' cell) + eta := by
    refine csSup_le hcell_nonempty ?_
    rintro _ ⟨x, hx, rfl⟩
    have hle_inf : f x - eta ≤ sInf (f '' cell) := by
      refine le_csInf hcell_nonempty ?_
      rintro _ ⟨y, hy, rfl⟩
      have hxy : f x - f y ≤ eta := (abs_le.mp (hosc x hx y hy)).2
      linarith
    linarith
  unfold upperStep lowerStep
  linarith

lemma abs_sub_le_cell_length_of_mem_subinterval {a b x y : ℝ}
    (P : Partition a b) {i : Fin P.n}
    (hx : x ∈ Partition.subinterval P i)
    (hy : y ∈ Partition.subinterval P i) :
    |x - y| ≤ P.pts i.succ - P.pts i.castSucc := by
  rcases hx with ⟨hix, hxi⟩
  rcases hy with ⟨hiy, hyi⟩
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

lemma partition_length_le_mesh_core {a b : ℝ}
    (P : Partition a b) (i : Fin P.n) :
    P.pts i.succ - P.pts i.castSucc ≤ P.mesh := by
  unfold Partition.mesh
  exact Finset.le_sup'
    (fun j : Fin P.n => P.pts j.succ - P.pts j.castSucc)
    (by simp : i ∈ (Finset.univ : Finset (Fin P.n)))

def ClosedIntervalDarbouxGapSmall
    (a b : ℝ) (f α : ℝ → ℝ) : Prop :=
  ∀ eps > 0, ∃ δ > 0, ∀ P : Partition a b,
    P.mesh < δ →
      upperSum P f α - lowerSum P f α < eps

private noncomputable def ptNat {a b : ℝ} (P : Partition a b) (k : ℕ) : ℝ :=
  if hk : k ≤ P.n then
    P.pts ⟨k, Nat.lt_succ_of_le hk⟩
  else
    P.pts (Fin.last P.n)

private lemma ptNat_zero {a b : ℝ} (P : Partition a b) :
    ptNat P 0 = a := by
  unfold ptNat
  rw [dif_pos (Nat.zero_le P.n)]
  simpa using P.pts_start

private lemma ptNat_last {a b : ℝ} (P : Partition a b) :
    ptNat P P.n = b := by
  unfold ptNat
  rw [dif_pos le_rfl]
  have hfin :
      (⟨P.n, Nat.lt_succ_self P.n⟩ : Fin (P.n + 1)) = Fin.last P.n := by
    ext
    simp
  simpa [hfin] using P.pts_end

private lemma ptNat_of_lt {a b : ℝ} (P : Partition a b) {k : ℕ}
    (hk : k < P.n) :
    ptNat P k = P.pts (Fin.castSucc (⟨k, hk⟩ : Fin P.n)) := by
  unfold ptNat
  rw [dif_pos (le_of_lt hk)]
  congr

private lemma ptNat_succ_of_lt {a b : ℝ} (P : Partition a b) {k : ℕ}
    (hk : k < P.n) :
    ptNat P (k + 1) = P.pts (Fin.succ (⟨k, hk⟩ : Fin P.n)) := by
  unfold ptNat
  rw [dif_pos (Nat.succ_le_of_lt hk)]
  congr

lemma partition_length_sum {a b : ℝ} (P : Partition a b) :
    (∑ i : Fin P.n, (P.pts i.succ - P.pts i.castSucc)) = b - a := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  have htel0 := Finset.sum_Ico_sub (ptNat P) (Nat.zero_le P.n)
  have hIco : Finset.Ico 0 P.n = Finset.range P.n := by
    ext k
    simp
  rw [hIco] at htel0
  have htel :
      (∑ k ∈ Finset.range P.n, (ptNat P (k + 1) - ptNat P k)) = b - a := by
    simpa [ptNat_zero, ptNat_last] using htel0
  trans (∑ k ∈ Finset.range P.n, (ptNat P (k + 1) - ptNat P k))
  · refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < P.n := Finset.mem_range.mp hk
    rw [ptNat_succ_of_lt P hklt, ptNat_of_lt P hklt]
    simp [hklt]
  · exact htel

theorem sourceHypotheses_of_continuous_derivative_integrator {f α : ℝ → ℝ}
    {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : MonotoneOn α (Set.Icc a b)) :
    SourceHypotheses a b f α := by
  refine ⟨hab, ?_, ?_, ?_⟩
  · exact (isCompact_Icc.image_of_continuousOn hf).bddAbove
  · exact (isCompact_Icc.image_of_continuousOn hf).bddBelow
  · exact hαmono

theorem derivative_integrand_continuousOn {f α' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b))
    (hα'cont : ContinuousOn α' (Set.Icc a b)) :
    ContinuousOn (fun x => f x * α' x) (Set.Icc a b) :=
  hf.mul hα'cont

theorem exists_pos_abs_bound_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, x ∈ Set.Icc a b → |f x| ≤ C := by
  exact exists_pos_abs_bound_on_Icc_of_bddAbove_bddBelow
    (isCompact_Icc.image_of_continuousOn hf).bddAbove
    (isCompact_Icc.image_of_continuousOn hf).bddBelow

lemma tag_mem_Icc {a b : ℝ} (P : Partition a b)
    {tags : Fin P.n → ℝ} (htags : tagsInPartition P tags)
    (i : Fin P.n) :
    tags i ∈ Set.Icc a b :=
  DarbouxRS.tag_mem_Icc_of_tagsInPartition_core P htags i

theorem exists_cell_deriv_eq_increment_slope {α α' : ℝ → ℝ} {a b u v : ℝ}
    (huv : u < v)
    (hsub : Set.Icc u v ⊆ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo u v, α' c = (α v - α u) / (v - u) := by
  refine exists_hasDerivAt_eq_slope α α' huv ?_ ?_
  · intro x hx
    exact (hderiv x (hsub hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact hderiv x (hsub (Set.Ioo_subset_Icc_self hx))

theorem exists_cell_increment_eq_deriv_mul_length {α α' : ℝ → ℝ} {a b u v : ℝ}
    (huv : u < v)
    (hsub : Set.Icc u v ⊆ Set.Icc a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo u v, α v - α u = α' c * (v - u) := by
  rcases exists_cell_deriv_eq_increment_slope huv hsub hderiv with
    ⟨c, hc, hcslope⟩
  refine ⟨c, hc, ?_⟩
  rw [hcslope]
  exact (div_mul_cancel₀ (α v - α u) (sub_ne_zero.mpr huv.ne')).symm

theorem cell_mvt_point {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x) :
    ∃ c ∈ Set.Ioo (P.pts i.castSucc) (P.pts i.succ),
      α (P.pts i.succ) - α (P.pts i.castSucc) =
        α' c * (P.pts i.succ - P.pts i.castSucc) := by
  exact exists_cell_increment_eq_deriv_mul_length
    (P.strict_mono Fin.castSucc_lt_succ)
    (DarbouxRS.subinterval_subset_Icc_core P (i := i))
    hαderiv

noncomputable def cellMVTTag {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) : ℝ :=
  Classical.choose (cell_mvt_point P i hαderiv)

theorem cellMVTTag_mem_Ioo {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    cellMVTTag P hαderiv i ∈
      Set.Ioo (P.pts i.castSucc) (P.pts i.succ) := by
  unfold cellMVTTag
  exact (Classical.choose_spec (cell_mvt_point P i hαderiv)).1

theorem cellMVTTag_increment_eq {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    α (P.pts i.succ) - α (P.pts i.castSucc) =
      α' (cellMVTTag P hαderiv i) *
        (P.pts i.succ - P.pts i.castSucc) := by
  unfold cellMVTTag
  exact (Classical.choose_spec (cell_mvt_point P i hαderiv)).2

theorem cellMVTTag_mem_subinterval {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    cellMVTTag P hαderiv i ∈ Partition.subinterval P i := by
  exact Set.Ioo_subset_Icc_self (cellMVTTag_mem_Ioo P hαderiv i)

theorem cellMVTTag_mem_Icc {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    cellMVTTag P hαderiv i ∈ Set.Icc a b :=
  DarbouxRS.subinterval_subset_Icc_core P
    (cellMVTTag_mem_subinterval P hαderiv i)

theorem tag_mvt_distance_le_mesh {α α' : ℝ → ℝ} {a b : ℝ}
    (P : Partition a b) {tags : Fin P.n → ℝ}
    (htags : tagsInPartition P tags)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (i : Fin P.n) :
    |cellMVTTag P hαderiv i - tags i| ≤ P.mesh := by
  have hcell :
      |cellMVTTag P hαderiv i - tags i| ≤
        P.pts i.succ - P.pts i.castSucc :=
    abs_sub_le_cell_length_of_mem_subinterval P
      (cellMVTTag_mem_subinterval P hαderiv i)
      (htags i)
  exact le_trans hcell (partition_length_le_mesh_core P i)

theorem taggedSum_derivative_identity_abs_le {f α α' : ℝ → ℝ} {a b C eta delta : ℝ}
    (P : Partition a b) (tags : Fin P.n → ℝ)
    (htags : tagsInPartition P tags)
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'osc :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |x - y| < delta → |α' x - α' y| ≤ eta)
    (hmesh : P.mesh < delta)
    (hbound : ∀ x : ℝ, x ∈ Set.Icc a b → |f x| ≤ C)
    (hC : 0 ≤ C) :
    |taggedSum P tags f α -
        taggedSum P tags (fun x => f x * α' x) (fun x => x)| ≤
      C * eta * (b - a) := by
  have hsum_rewrite :
      taggedSum P tags f α -
          taggedSum P tags (fun x => f x * α' x) (fun x => x) =
        ∑ i : Fin P.n,
          (f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
            (f (tags i) * α' (tags i)) *
              (P.pts i.succ - P.pts i.castSucc)) := by
    unfold taggedSum
    rw [← Finset.sum_sub_distrib]
  calc
    |taggedSum P tags f α -
        taggedSum P tags (fun x => f x * α' x) (fun x => x)|
        =
      |∑ i : Fin P.n,
          (f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
            (f (tags i) * α' (tags i)) *
              (P.pts i.succ - P.pts i.castSucc))| := by
        rw [hsum_rewrite]
    _ ≤ ∑ i : Fin P.n,
          |f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
            (f (tags i) * α' (tags i)) *
              (P.pts i.succ - P.pts i.castSucc)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin P.n,
          C * eta * (P.pts i.succ - P.pts i.castSucc) := by
        refine Finset.sum_le_sum ?_
        intro i _hi
        let c := cellMVTTag P hαderiv i
        have hc_eq :
            α (P.pts i.succ) - α (P.pts i.castSucc) =
              α' c * (P.pts i.succ - P.pts i.castSucc) := by
          simpa [c] using cellMVTTag_increment_eq P hαderiv i
        have htagI : tags i ∈ Set.Icc a b := tag_mem_Icc P htags i
        have hcI : c ∈ Set.Icc a b := by
          simpa [c] using cellMVTTag_mem_Icc P hαderiv i
        have hdist : |c - tags i| < delta := by
          have hle : |c - tags i| ≤ P.mesh := by
            simpa [c] using tag_mvt_distance_le_mesh P htags hαderiv i
          exact lt_of_le_of_lt hle hmesh
        have hosc : |α' c - α' (tags i)| ≤ eta :=
          hα'osc c hcI (tags i) htagI hdist
        have hfbound : |f (tags i)| ≤ C := hbound (tags i) htagI
        have hlen_nonneg : 0 ≤ P.pts i.succ - P.pts i.castSucc :=
          sub_nonneg.mpr (le_of_lt (P.strict_mono Fin.castSucc_lt_succ))
        have hprod :
            |f (tags i)| * |α' c - α' (tags i)| *
                (P.pts i.succ - P.pts i.castSucc) ≤
              C * eta * (P.pts i.succ - P.pts i.castSucc) := by
          have hmul₁ :
              |f (tags i)| * |α' c - α' (tags i)| ≤ C * eta :=
            mul_le_mul hfbound hosc (abs_nonneg _) hC
          exact mul_le_mul_of_nonneg_right hmul₁ hlen_nonneg
        have hterm_eq :
            f (tags i) * (α (P.pts i.succ) - α (P.pts i.castSucc)) -
                (f (tags i) * α' (tags i)) *
                  (P.pts i.succ - P.pts i.castSucc) =
              f (tags i) * (α' c - α' (tags i)) *
                (P.pts i.succ - P.pts i.castSucc) := by
          rw [hc_eq]
          ring
        rw [hterm_eq, abs_mul, abs_mul, abs_of_nonneg hlen_nonneg]
        exact hprod
    _ = C * eta * (b - a) := by
        rw [← Finset.mul_sum]
        rw [partition_length_sum P]

theorem cell_integral_between_lower_upper_id {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) (i : Fin P.n) :
    lowerStep P g i * (P.pts i.succ - P.pts i.castSucc) ≤
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x ∧
      ∫ x in P.pts i.castSucc..P.pts i.succ, g x ≤
        upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
  have huv : P.pts i.castSucc ≤ P.pts i.succ :=
    le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
  have hgcell :
      ContinuousOn g (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) :=
    hg.mono (DarbouxRS.subinterval_subset_Icc_core P (i := i))
  have hgi : IntervalIntegrable g volume (P.pts i.castSucc) (P.pts i.succ) :=
    ContinuousOn.intervalIntegrable_of_Icc huv hgcell
  have hconstLower :
      IntervalIntegrable (fun _ : ℝ => lowerStep P g i) volume
        (P.pts i.castSucc) (P.pts i.succ) :=
    continuous_const.intervalIntegrable _ _
  have hconstUpper :
      IntervalIntegrable (fun _ : ℝ => upperStep P g i) volume
        (P.pts i.castSucc) (P.pts i.succ) :=
    continuous_const.intervalIntegrable _ _
  have hcellBelow : BddBelow (g '' Partition.subinterval P i) := by
    simpa [Partition.subinterval] using
      (isCompact_Icc.image_of_continuousOn hgcell).bddBelow
  have hcellAbove : BddAbove (g '' Partition.subinterval P i) := by
    simpa [Partition.subinterval] using
      (isCompact_Icc.image_of_continuousOn hgcell).bddAbove
  have hLowerPoint :
      ∀ x ∈ Set.Icc (P.pts i.castSucc) (P.pts i.succ),
        lowerStep P g i ≤ g x := by
    intro x hx
    unfold lowerStep
    exact csInf_le hcellBelow ⟨x, hx, rfl⟩
  have hUpperPoint :
      ∀ x ∈ Set.Icc (P.pts i.castSucc) (P.pts i.succ),
        g x ≤ upperStep P g i := by
    intro x hx
    unfold upperStep
    exact le_csSup hcellAbove ⟨x, hx, rfl⟩
  have hLowerIntegral :
      (∫ x in P.pts i.castSucc..P.pts i.succ, lowerStep P g i) ≤
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x :=
    intervalIntegral.integral_mono_on huv hconstLower hgi hLowerPoint
  have hUpperIntegral :
      (∫ x in P.pts i.castSucc..P.pts i.succ, g x) ≤
        ∫ x in P.pts i.castSucc..P.pts i.succ, upperStep P g i :=
    intervalIntegral.integral_mono_on huv hgi hconstUpper hUpperPoint
  constructor
  · calc
      lowerStep P g i * (P.pts i.succ - P.pts i.castSucc)
          = ∫ x in P.pts i.castSucc..P.pts i.succ, lowerStep P g i := by
            rw [intervalIntegral.integral_const]
            simp [smul_eq_mul, mul_comm]
      _ ≤ ∫ x in P.pts i.castSucc..P.pts i.succ, g x := hLowerIntegral
  · calc
      ∫ x in P.pts i.castSucc..P.pts i.succ, g x
          ≤ ∫ x in P.pts i.castSucc..P.pts i.succ, upperStep P g i :=
            hUpperIntegral
      _ = upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
            rw [intervalIntegral.integral_const]
            simp [smul_eq_mul, mul_comm]

private lemma partition_integral_sum {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) :
    (∑ i : Fin P.n,
        ∫ x in P.pts i.castSucc..P.pts i.succ, g x) =
      ∫ x in a..b, g x := by
  classical
  rw [Finset.sum_fin_eq_sum_range]

  have hcellIntNat :
      ∀ k < P.n, IntervalIntegrable g volume (ptNat P k) (ptNat P (k + 1)) := by
    intro k hk
    let i : Fin P.n := ⟨k, hk⟩
    have huv : P.pts i.castSucc ≤ P.pts i.succ :=
      le_of_lt (P.strict_mono Fin.castSucc_lt_succ)
    have hgcell :
        ContinuousOn g (Set.Icc (P.pts i.castSucc) (P.pts i.succ)) :=
      hg.mono (DarbouxRS.subinterval_subset_Icc_core P (i := i))
    have hInt :
        IntervalIntegrable g volume (P.pts i.castSucc) (P.pts i.succ) :=
      ContinuousOn.intervalIntegrable_of_Icc huv hgcell

    have hleft : ptNat P k = P.pts i.castSucc := by
      rw [ptNat_of_lt P hk]

    have hright : ptNat P (k + 1) = P.pts i.succ := by
      rw [ptNat_succ_of_lt P hk]

    simpa [hleft, hright] using hInt

  have hsum0 :=
    intervalIntegral.sum_integral_adjacent_intervals hcellIntNat

  have hsum :
      (∑ k ∈ Finset.range P.n,
          ∫ x in ptNat P k..ptNat P (k + 1), g x) =
        ∫ x in a..b, g x := by
    simpa [ptNat_zero, ptNat_last] using hsum0

  trans
      (∑ k ∈ Finset.range P.n,
          ∫ x in ptNat P k..ptNat P (k + 1), g x)
  · refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < P.n := Finset.mem_range.mp hk
    rw [dif_pos hklt]
    rw [ptNat_of_lt P hklt, ptNat_succ_of_lt P hklt]

  · exact hsum

theorem partition_integral_between_lower_upper_id {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Set.Icc a b))
    (P : Partition a b) :
    lowerSum P g (fun x => x) ≤ ∫ x in a..b, g x ∧
      ∫ x in a..b, g x ≤ upperSum P g (fun x => x) := by
  have hsumIntegral := partition_integral_sum hg P
  have hlowerSum :
      (∑ i : Fin P.n,
          lowerStep P g i * (P.pts i.succ - P.pts i.castSucc)) ≤
        ∑ i : Fin P.n,
          ∫ x in P.pts i.castSucc..P.pts i.succ, g x := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact (cell_integral_between_lower_upper_id hg P i).1
  have hupperSum :
      (∑ i : Fin P.n,
          ∫ x in P.pts i.castSucc..P.pts i.succ, g x) ≤
        ∑ i : Fin P.n,
          upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact (cell_integral_between_lower_upper_id hg P i).2
  constructor
  · calc
      lowerSum P g (fun x => x)
          = ∑ i : Fin P.n,
              lowerStep P g i * (P.pts i.succ - P.pts i.castSucc) := by
            unfold lowerSum
            simp
      _ ≤ ∑ i : Fin P.n,
            ∫ x in P.pts i.castSucc..P.pts i.succ, g x := hlowerSum
      _ = ∫ x in a..b, g x := hsumIntegral
  · calc
      ∫ x in a..b, g x
          = ∑ i : Fin P.n,
              ∫ x in P.pts i.castSucc..P.pts i.succ, g x :=
            hsumIntegral.symm
      _ ≤ ∑ i : Fin P.n,
            upperStep P g i * (P.pts i.succ - P.pts i.castSucc) := hupperSum
      _ = upperSum P g (fun x => x) := by
            unfold upperSum
            simp

theorem upper_lower_gap_small_continuous_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    ClosedIntervalDarbouxGapSmall a b g (fun x => x) := by
  intro eps heps
  let eta : ℝ := eps / (b - a + 1)
  have hspan_nonneg : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt hab)
  have hden_pos : 0 < b - a + 1 := by linarith
  have heta_pos : 0 < eta := div_pos heps hden_pos
  have hsmall_eta_span : eta * (b - a) < eps := by
    have hspan_lt : b - a < b - a + 1 := by linarith
    have hmul_lt := mul_lt_mul_of_pos_left hspan_lt heta_pos
    have heta_den : eta * (b - a + 1) = eps := by
      dsimp [eta]
      field_simp [ne_of_gt hden_pos]
    linarith
  have hunif : UniformContinuousOn g (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  rcases (Metric.uniformContinuousOn_iff.mp hunif eta heta_pos) with
    ⟨δ, hδ_pos, Hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro P hmesh
  have hAbove : BddAbove (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddAbove
  have hBelow : BddBelow (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddBelow
  have hstep :
      ∀ i : Fin P.n,
        upperStep P g i - lowerStep P g i ≤ eta := by
    intro i
    refine upperStep_sub_lowerStep_le_of_subinterval_oscillation_bound
      P i hAbove hBelow ?_
    intro x hx y hy
    have hxI : x ∈ Set.Icc a b :=
      DarbouxRS.subinterval_subset_Icc_core P hx
    have hyI : y ∈ Set.Icc a b :=
      DarbouxRS.subinterval_subset_Icc_core P hy
    have hxy_len : |x - y| ≤ P.pts i.succ - P.pts i.castSucc :=
      abs_sub_le_cell_length_of_mem_subinterval P hx hy
    have hlen_mesh : P.pts i.succ - P.pts i.castSucc ≤ P.mesh :=
      partition_length_le_mesh_core P i
    have hdist : dist x y < δ := by
      simpa [Real.dist_eq] using
        lt_of_le_of_lt (le_trans hxy_len hlen_mesh) hmesh
    exact le_of_lt (by
      simpa [Real.dist_eq] using Hδ x hxI y hyI hdist)
  have hosc_le :
      partitionOscillation P g (fun x => x) ≤ eta * (b - a) := by
    unfold partitionOscillation
    calc
      (∑ i : Fin P.n,
          (upperStep P g i - lowerStep P g i) *
            ((fun x : ℝ => x) (P.pts i.succ) -
              (fun x : ℝ => x) (P.pts i.castSucc)))
          ≤ ∑ i : Fin P.n,
              eta * (P.pts i.succ - P.pts i.castSucc) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            have hlen_nonneg : 0 ≤ P.pts i.succ - P.pts i.castSucc :=
              sub_nonneg.mpr (le_of_lt (P.strict_mono Fin.castSucc_lt_succ))
            simpa using mul_le_mul_of_nonneg_right (hstep i) hlen_nonneg
      _ = eta * (b - a) := by
            rw [← Finset.mul_sum, partition_length_sum P]
  calc
    upperSum P g (fun x => x) - lowerSum P g (fun x => x)
        = partitionOscillation P g (fun x => x) :=
          upperSum_sub_lowerSum_eq_partitionOscillation P
    _ ≤ eta * (b - a) := hosc_le
    _ < eps := hsmall_eta_span

theorem rsUpperLowerCommonLimit_intervalIntegral_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    rsUpperLowerCommonLimit a b g (fun x => x) (∫ x in a..b, g x) := by
  have hAbove : BddAbove (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddAbove
  have hBelow : BddBelow (g '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hg).bddBelow
  refine ⟨⟨hab, hAbove, hBelow, monotoneOn_id⟩, ?_⟩
  intro eps heps
  rcases upper_lower_gap_small_continuous_id hab hg eps heps with
    ⟨δ, hδ_pos, Hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro P hmesh
  have hbetween := partition_integral_between_lower_upper_id hg P
  have hgap := Hδ P hmesh
  constructor
  · refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith
  · refine abs_lt.mpr ⟨?_, ?_⟩ <;> linarith

theorem rsTaggedCommonLimit_intervalIntegral_id {g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hg : ContinuousOn g (Set.Icc a b)) :
    rsTaggedCommonLimit a b g (fun x => x) (∫ x in a..b, g x) :=
  taggedCommonLimit_of_upperLowerCommonLimit
    (rsUpperLowerCommonLimit_intervalIntegral_id hab hg)

theorem rsTaggedCommonLimit_derivative_of_identity_tagged_limit
    {f α α' : ℝ → ℝ} {a b L : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : MonotoneOn α (Set.Icc a b))
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Set.Icc a b))
    (hId : rsTaggedCommonLimit a b (fun x => f x * α' x) (fun x => x) L) :
    rsTaggedCommonLimit a b f α L := by
  refine ⟨sourceHypotheses_of_continuous_derivative_integrator hab hf hαmono, ?_⟩
  intro eps heps
  rcases exists_pos_abs_bound_of_continuousOn hf with ⟨C, hCpos, hCbound⟩
  let eta : ℝ := eps / (4 * C * (b - a))
  have hspan_pos : 0 < b - a := sub_pos.mpr hab
  have hden_pos : 0 < 4 * C * (b - a) := by positivity
  have heta_pos : 0 < eta := div_pos heps hden_pos
  have hdiff_budget : C * eta * (b - a) < eps / 2 := by
    have hcalc : C * eta * (b - a) = eps / 4 := by
      dsimp [eta]
      field_simp [ne_of_gt hCpos, ne_of_gt hspan_pos]
    linarith
  have hunif : UniformContinuousOn α' (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hα'cont
  rcases (Metric.uniformContinuousOn_iff.mp hunif eta heta_pos) with
    ⟨δA, hδApos, HδA⟩
  rcases hId with ⟨_hsId, hlimId⟩
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimId (eps / 2) hhalf with ⟨δI, hδIpos, HδI⟩
  refine ⟨min δA δI, lt_min hδApos hδIpos, ?_⟩
  intro P tags htags hmesh
  have hmeshA : P.mesh < δA := lt_of_lt_of_le hmesh (min_le_left δA δI)
  have hmeshI : P.mesh < δI := lt_of_lt_of_le hmesh (min_le_right δA δI)
  have hα'osc :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |x - y| < δA → |α' x - α' y| ≤ eta := by
    intro x hx y hy hxy
    have hdist : dist x y < δA := by
      simpa [Real.dist_eq] using hxy
    have h := HδA x hx y hy hdist
    exact le_of_lt (by simpa [Real.dist_eq] using h)
  let Sid : ℝ := taggedSum P tags (fun x => f x * α' x) (fun x => x)
  have hdiff :
      |taggedSum P tags f α - Sid| < eps / 2 := by
    have hle :
        |taggedSum P tags f α - Sid| ≤ C * eta * (b - a) := by
      simpa [Sid] using
        taggedSum_derivative_identity_abs_le
          (f := f) (α := α) (α' := α') (a := a) (b := b)
          (C := C) (eta := eta) (delta := δA)
          P tags htags hαderiv hα'osc hmeshA hCbound (le_of_lt hCpos)
    exact lt_of_le_of_lt hle hdiff_budget
  have hIdClose : |Sid - L| < eps / 2 := by
    simpa [Sid] using HδI P tags htags hmeshI
  have htriangle :
      |taggedSum P tags f α - L| ≤
        |taggedSum P tags f α - Sid| + |Sid - L| := by
    have hdecomp :
        taggedSum P tags f α - L =
          (taggedSum P tags f α - Sid) + (Sid - L) := by
      ring
    rw [hdecomp]
    exact abs_add_le _ _
  calc
    |taggedSum P tags f α - L|
        ≤ |taggedSum P tags f α - Sid| + |Sid - L| := htriangle
    _ < eps / 2 + eps / 2 := add_lt_add hdiff hIdClose
    _ = eps := by ring

theorem rsTaggedCommonLimit_integral_deriv
    {f α α' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hαmono : MonotoneOn α (Set.Icc a b))
    (hαderiv : ∀ x ∈ Set.Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Set.Icc a b)) :
    rsTaggedCommonLimit a b f α (∫ x in a..b, f x * α' x) := by
  exact rsTaggedCommonLimit_derivative_of_identity_tagged_limit
    hab hf hαmono hαderiv hα'cont
    (rsTaggedCommonLimit_intervalIntegral_id hab
      (derivative_integrand_continuousOn hf hα'cont))

end Thm_1_4

theorem thm_1_4 {f α α' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hαmono : MonotoneOn α (Icc a b))
    (hαderiv : ∀ x ∈ Icc a b, HasDerivAt α (α' x) x)
    (hα'cont : ContinuousOn α' (Icc a b))
    (hRS : RSIntegrable f α a b) :
    IntervalIntegrable (fun x => f x * α' x) volume a b ∧
      rsIntegral f α a b hRS = ∫ x in a..b, f x * α' x := by
  have hInt :
      IntervalIntegrable (fun x => f x * α' x) volume a b :=
    (hf.mul hα'cont).intervalIntegrable_of_Icc hab
  have hstrict : a < b :=
    Thm_1_4.strict_interval_of_rsIntegrable hRS
  have hTagged :
      rsTaggedCommonLimit a b f α (∫ x in a..b, f x * α' x) :=
    Thm_1_4.rsTaggedCommonLimit_integral_deriv
      hstrict hf hαmono hαderiv hα'cont
  refine ⟨hInt, ?_⟩
  exact taggedCommonLimit_unique (rsIntegral_spec hRS) hTagged
