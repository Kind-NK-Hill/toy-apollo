import ToyApollo.Output.rs_stieltjes_measure_bridge

open MeasureTheory intervalIntegral Set
open scoped Pointwise

noncomputable section

/-!
Darboux algebra and congruence support for the local RS bridge family.
This is a mechanical split from the old mixed `rs_stieltjes_bridge` body.
-/
namespace DarbouxRS

lemma partition_pts_monotone {a b : ℝ} (P : Partition a b) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ P.n) : P.pts i ≤ P.pts j := by
  induction j generalizing i with
  | zero =>
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hij
      subst hi0
      rfl
  | succ j ih =>
      by_cases htop : i = j + 1
      · subst htop
        rfl
      · have hij' : i ≤ j := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hij htop)
        have hjle : j ≤ P.n := Nat.le_trans (Nat.le_succ j) hj
        have hlt : j < P.n := Nat.lt_of_succ_le hj
        exact le_trans (ih hij' hjle) (le_of_lt (P.strict_mono j hlt))

lemma partition_pts_mem_Icc {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) :
    P.pts i ∈ Icc a b := by
  constructor
  · calc
      a = P.pts 0 := P.pts_start.symm
      _ ≤ P.pts i := partition_pts_monotone P (Nat.zero_le i) hi
  · calc
      P.pts i ≤ P.pts P.n := partition_pts_monotone P hi le_rfl
      _ = b := P.pts_end

lemma subinterval_subset_Icc {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    subinterval P i ⊆ Icc a b := by
  intro x hx
  constructor
  · exact le_trans (partition_pts_mem_Icc P (Nat.le_of_lt hi)).1 hx.1
  · exact le_trans hx.2 (partition_pts_mem_Icc P (Nat.succ_le_of_lt hi)).2

lemma partition_length_le_mesh {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i < P.n) :
    P.pts (i + 1) - P.pts i ≤ P.mesh := by
  unfold Partition.mesh
  exact Finset.le_sup' (s := Finset.range P.n)
    (f := fun j => P.pts (j + 1) - P.pts j) (Finset.mem_range.mpr hi)

lemma singleJumpStep_monotone {c u₁ u₂ : ℝ} (hu : u₁ ≤ u₂) :
    Monotone (fun x : ℝ => if x < c then u₁ else u₂) := by
  intro x y hxy
  by_cases hy : y < c
  · have hx : x < c := lt_of_le_of_lt hxy hy
    simp [hx, hy]
  · by_cases hx : x < c
    · simp [hx, hy, hu]
    · simp [hx, hy]

lemma singleJump_increment_nonneg {c u₁ u₂ : ℝ} (hu : u₁ ≤ u₂)
    {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ (if y < c then u₁ else u₂) - (if x < c then u₁ else u₂) := by
  exact sub_nonneg.mpr (singleJumpStep_monotone hu hxy)

lemma singleJump_increment_ne_zero_crosses {x y c u₁ u₂ : ℝ}
    (hxy : x ≤ y)
    (hne : (if y < c then u₁ else u₂) - (if x < c then u₁ else u₂) ≠ 0) :
    x < c ∧ c ≤ y := by
  by_cases hx : x < c
  · by_cases hy : y < c
    · simp [hx, hy] at hne
    · exact ⟨hx, le_of_not_gt hy⟩
  · have hy : ¬ y < c := not_lt.mpr ((le_of_not_gt hx).trans hxy)
    simp [hx, hy] at hne

lemma singleJump_partition_increment_sum {a b c u₁ u₂ : ℝ}
    (P : Partition a b) (hac : a < c) (hcb : c ≤ b) :
    ∑ i ∈ Finset.range P.n,
      ((if P.pts (i + 1) < c then u₁ else u₂) -
        (if P.pts i < c then u₁ else u₂)) = u₂ - u₁ := by
  have hsum := Finset.sum_range_sub (fun j => if P.pts j < c then u₁ else u₂) P.n
  have h0 : P.pts 0 < c := by simpa [P.pts_start] using hac
  have hn : ¬ P.pts P.n < c := by
    have : c ≤ P.pts P.n := by simpa [P.pts_end] using hcb
    exact not_lt.mpr this
  simpa [h0, hn] using hsum

lemma singleJump_taggedSum_sub_value {a b c u₁ u₂ : ℝ}
    (P : Partition a b) (tags : ℕ → ℝ) (f : ℝ → ℝ)
    (hac : a < c) (hcb : c ≤ b) :
    taggedSum P tags f (fun x => if x < c then u₁ else u₂) - f c * (u₂ - u₁) =
      ∑ i ∈ Finset.range P.n,
        ((f (tags i) - f c) *
          ((if P.pts (i + 1) < c then u₁ else u₂) -
            (if P.pts i < c then u₁ else u₂))) := by
  have hsum := singleJump_partition_increment_sum
    (P := P) (c := c) (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)
  unfold taggedSum
  rw [← hsum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

lemma singleJump_upperSum_sub_value {a b c u₁ u₂ : ℝ}
    (P : Partition a b) (f : ℝ → ℝ) (hac : a < c) (hcb : c ≤ b) :
    upperSum P f (fun x => if x < c then u₁ else u₂) - f c * (u₂ - u₁) =
      ∑ i ∈ Finset.range P.n,
        ((upperStep P f i - f c) *
          ((if P.pts (i + 1) < c then u₁ else u₂) -
            (if P.pts i < c then u₁ else u₂))) := by
  have hsum := singleJump_partition_increment_sum
    (P := P) (c := c) (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)
  unfold upperSum
  rw [← hsum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

lemma singleJump_lowerSum_sub_value {a b c u₁ u₂ : ℝ}
    (P : Partition a b) (f : ℝ → ℝ) (hac : a < c) (hcb : c ≤ b) :
    lowerSum P f (fun x => if x < c then u₁ else u₂) - f c * (u₂ - u₁) =
      ∑ i ∈ Finset.range P.n,
        ((lowerStep P f i - f c) *
          ((if P.pts (i + 1) < c then u₁ else u₂) -
            (if P.pts i < c then u₁ else u₂))) := by
  have hsum := singleJump_partition_increment_sum
    (P := P) (c := c) (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)
  unfold lowerSum
  rw [← hsum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

lemma crossing_tag_abs_sub_le_mesh {a b c : ℝ} {P : Partition a b} {tags : ℕ → ℝ}
    {i : ℕ} (hi : i < P.n) (htags : tagsInPartition P tags)
    (hcross : P.pts i < c ∧ c ≤ P.pts (i + 1)) :
    |tags i - c| ≤ P.mesh := by
  have ht := htags i hi
  have hlen : P.pts (i + 1) - P.pts i ≤ P.mesh := partition_length_le_mesh P hi
  have habs : |tags i - c| ≤ P.pts (i + 1) - P.pts i := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [ht.1, hcross.2]
    · nlinarith [ht.2, le_of_lt hcross.1]
  exact le_trans habs hlen

lemma crossing_point_abs_sub_le_mesh {a b c x : ℝ} {P : Partition a b} {i : ℕ}
    (hi : i < P.n) (hx : x ∈ subinterval P i)
    (hcross : P.pts i < c ∧ c ≤ P.pts (i + 1)) :
    |x - c| ≤ P.mesh := by
  have hlen : P.pts (i + 1) - P.pts i ≤ P.mesh := partition_length_le_mesh P hi
  have habs : |x - c| ≤ P.pts (i + 1) - P.pts i := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [hx.1, hcross.2]
    · nlinarith [hx.2, le_of_lt hcross.1]
  exact le_trans habs hlen

lemma upperStep_abs_sub_le_of_crossing {a b c eta : ℝ} {P : Partition a b}
    {f : ℝ → ℝ} {i : ℕ} (hi : i < P.n)
    (hAbove : BddAbove (f '' Icc a b))
    (hcross : P.pts i < c ∧ c ≤ P.pts (i + 1))
    (hclose : ∀ x ∈ subinterval P i, |f x - f c| < eta) :
    |upperStep P f i - f c| ≤ eta := by
  have hcell_nonempty : (f '' subinterval P i).Nonempty := by
    refine ⟨f (P.pts i), ?_⟩
    exact ⟨P.pts i, ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩, rfl⟩
  have hcell_above : BddAbove (f '' subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc P hi)) hAbove
  have hupper_le : upperStep P f i ≤ f c + eta := by
    unfold upperStep
    refine csSup_le hcell_nonempty ?_
    rintro y ⟨x, hx, rfl⟩
    have hxclose := hclose x hx
    have hright := (abs_lt.mp hxclose).2
    linarith
  have hfc_le_upper : f c ≤ upperStep P f i := by
    unfold upperStep
    exact le_csSup hcell_above ⟨c, ⟨le_of_lt hcross.1, hcross.2⟩, rfl⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma lowerStep_abs_sub_le_of_crossing {a b c eta : ℝ} {P : Partition a b}
    {f : ℝ → ℝ} {i : ℕ} (hi : i < P.n)
    (hBelow : BddBelow (f '' Icc a b))
    (hcross : P.pts i < c ∧ c ≤ P.pts (i + 1))
    (hclose : ∀ x ∈ subinterval P i, |f x - f c| < eta) :
    |lowerStep P f i - f c| ≤ eta := by
  have hcell_nonempty : (f '' subinterval P i).Nonempty := by
    refine ⟨f (P.pts i), ?_⟩
    exact ⟨P.pts i, ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩, rfl⟩
  have hcell_below : BddBelow (f '' subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc P hi)) hBelow
  have hlower_ge : f c - eta ≤ lowerStep P f i := by
    unfold lowerStep
    refine le_csInf hcell_nonempty ?_
    rintro y ⟨x, hx, rfl⟩
    have hxclose := hclose x hx
    have hleft := (abs_lt.mp hxclose).1
    linarith
  have hlower_le_fc : lowerStep P f i ≤ f c := by
    unfold lowerStep
    exact csInf_le hcell_below ⟨c, ⟨le_of_lt hcross.1, hcross.2⟩, rfl⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma upperStep_integrand_add_le {a b : ℝ} (P : Partition a b)
    {f g : ℝ → ℝ} {i : ℕ} (hi : i < P.n)
    (hfAbove : BddAbove (f '' Icc a b))
    (hgAbove : BddAbove (g '' Icc a b)) :
    upperStep P (fun x => f x + g x) i ≤ upperStep P f i + upperStep P g i := by
  have hcell_nonempty : ((fun x => f x + g x) '' subinterval P i).Nonempty := by
    refine ⟨f (P.pts i) + g (P.pts i), ?_⟩
    exact ⟨P.pts i, ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩, rfl⟩
  have hfCellAbove : BddAbove (f '' subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc P hi)) hfAbove
  have hgCellAbove : BddAbove (g '' subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc P hi)) hgAbove
  unfold upperStep
  refine csSup_le hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩
  have hfx : f x ≤ sSup (f '' subinterval P i) :=
    le_csSup hfCellAbove ⟨x, hx, rfl⟩
  have hgx : g x ≤ sSup (g '' subinterval P i) :=
    le_csSup hgCellAbove ⟨x, hx, rfl⟩
  linarith

lemma lowerStep_integrand_add_le {a b : ℝ} (P : Partition a b)
    {f g : ℝ → ℝ} {i : ℕ} (hi : i < P.n)
    (hfBelow : BddBelow (f '' Icc a b))
    (hgBelow : BddBelow (g '' Icc a b)) :
    lowerStep P f i + lowerStep P g i ≤ lowerStep P (fun x => f x + g x) i := by
  have hcell_nonempty : ((fun x => f x + g x) '' subinterval P i).Nonempty := by
    refine ⟨f (P.pts i) + g (P.pts i), ?_⟩
    exact ⟨P.pts i, ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩, rfl⟩
  have hfCellBelow : BddBelow (f '' subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc P hi)) hfBelow
  have hgCellBelow : BddBelow (g '' subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc P hi)) hgBelow
  unfold lowerStep
  refine le_csInf hcell_nonempty ?_
  rintro y ⟨x, hx, rfl⟩
  have hfx : sInf (f '' subinterval P i) ≤ f x :=
    csInf_le hfCellBelow ⟨x, hx, rfl⟩
  have hgx : sInf (g '' subinterval P i) ≤ g x :=
    csInf_le hgCellBelow ⟨x, hx, rfl⟩
  linarith

lemma partition_increment_nonneg_of_source {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) {i : ℕ} (hi : i < P.n) :
    0 ≤ alpha (P.pts (i + 1)) - alpha (P.pts i) := by
  rcases hs with ⟨_hab, _hAbove, _hBelow, hmono⟩
  have hleft : P.pts i ∈ Icc a b := partition_pts_mem_Icc P (Nat.le_of_lt hi)
  have hright : P.pts (i + 1) ∈ Icc a b := partition_pts_mem_Icc P (Nat.succ_le_of_lt hi)
  exact sub_nonneg.mpr (hmono hleft hright (le_of_lt (P.strict_mono i hi)))

theorem upperSum_integrand_add_le {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    upperSum P (fun x => f x + g x) alpha ≤
      upperSum P f alpha + upperSum P g alpha := by
  rcases hsf with ⟨hab, hfAbove, hfBelow, hmono⟩
  rcases hsg with ⟨_habg, hgAbove, _hgBelow, _hmonog⟩
  unfold upperSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have hstep := upperStep_integrand_add_le (P := P) (i := i) hi_lt hfAbove hgAbove
  have hinc : 0 ≤ alpha (P.pts (i + 1)) - alpha (P.pts i) := by
    exact partition_increment_nonneg_of_source P
      ⟨hab, hfAbove, hfBelow, hmono⟩ hi_lt
  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith

theorem lowerSum_integrand_add_le {a b : ℝ} (P : Partition a b)
    {f g alpha : ℝ → ℝ}
    (hsf : SourceHypotheses a b f alpha)
    (hsg : SourceHypotheses a b g alpha) :
    lowerSum P f alpha + lowerSum P g alpha ≤
      lowerSum P (fun x => f x + g x) alpha := by
  rcases hsf with ⟨hab, hfAbove, hfBelow, hmono⟩
  rcases hsg with ⟨_habg, _hgAbove, hgBelow, _hmonog⟩
  unfold lowerSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have hstep := lowerStep_integrand_add_le (P := P) (i := i) hi_lt hfBelow hgBelow
  have hinc : 0 ≤ alpha (P.pts (i + 1)) - alpha (P.pts i) := by
    exact partition_increment_nonneg_of_source P
      ⟨hab, hfAbove, hfBelow, hmono⟩ hi_lt
  have hmul := mul_le_mul_of_nonneg_right hstep hinc
  nlinarith

lemma lowerStep_le_upperStep {a b : ℝ} (P : Partition a b)
    {f : ℝ → ℝ} {i : ℕ} (hi : i < P.n)
    (hBelow : BddBelow (f '' Icc a b))
    (hAbove : BddAbove (f '' Icc a b)) :
    lowerStep P f i ≤ upperStep P f i := by
  have hcell_nonempty : (f '' subinterval P i).Nonempty := by
    refine ⟨f (P.pts i), ?_⟩
    exact ⟨P.pts i, ⟨le_rfl, le_of_lt (P.strict_mono i hi)⟩, rfl⟩
  have hcellBelow : BddBelow (f '' subinterval P i) :=
    BddBelow.mono (Set.image_mono (subinterval_subset_Icc P hi)) hBelow
  have hcellAbove : BddAbove (f '' subinterval P i) :=
    BddAbove.mono (Set.image_mono (subinterval_subset_Icc P hi)) hAbove
  rcases hcell_nonempty with ⟨y, hy⟩
  unfold lowerStep upperStep
  exact le_trans (csInf_le hcellBelow hy) (le_csSup hcellAbove hy)

theorem lowerSum_le_upperSum {a b : ℝ} (P : Partition a b)
    {f alpha : ℝ → ℝ} (hs : SourceHypotheses a b f alpha) :
    lowerSum P f alpha ≤ upperSum P f alpha := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  unfold lowerSum upperSum
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have hstep := lowerStep_le_upperStep (P := P) (i := i) hi_lt hBelow hAbove
  have hinc : 0 ≤ alpha (P.pts (i + 1)) - alpha (P.pts i) := by
    exact partition_increment_nonneg_of_source P
      ⟨hab, hAbove, hBelow, hmono⟩ hi_lt
  exact mul_le_mul_of_nonneg_right hstep hinc

lemma tag_mem_Icc_of_tagsInPartition {a b : ℝ} (P : Partition a b)
    {tags : ℕ → ℝ} (htags : tagsInPartition P tags)
    {i : ℕ} (hi : i < P.n) :
    tags i ∈ Icc a b :=
  subinterval_subset_Icc P hi (htags i hi)

theorem taggedSum_mono {a b : ℝ} (P : Partition a b) (tags : ℕ → ℝ)
    {f g alpha : ℝ → ℝ}
    (hs : SourceHypotheses a b f alpha)
    (htags : tagsInPartition P tags)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    taggedSum P tags f alpha ≤ taggedSum P tags g alpha := by
  rcases hs with ⟨hab, hAbove, hBelow, hmono⟩
  unfold taggedSum
  refine Finset.sum_le_sum ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have htag : tags i ∈ Icc a b := tag_mem_Icc_of_tagsInPartition P htags hi_lt
  have hstep : f (tags i) ≤ g (tags i) := hfg (tags i) htag
  have hinc : 0 ≤ alpha (P.pts (i + 1)) - alpha (P.pts i) := by
    exact partition_increment_nonneg_of_source P
      ⟨hab, hAbove, hBelow, hmono⟩ hi_lt
  exact mul_le_mul_of_nonneg_right hstep hinc

theorem taggedCommonLimit_mono {a b : ℝ} {f g alpha : ℝ → ℝ} {Lf Lg : ℝ}
    (hf : TaggedCommonLimit a b f alpha Lf)
    (hg : TaggedCommonLimit a b g alpha Lg)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) :
    Lf ≤ Lg := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨_hsg, hlimg⟩
  rcases hsf with ⟨hab, hAbove, hBelow, hmono⟩
  rw [le_iff_forall_pos_lt_add]
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  rcases exists_partition_mesh_lt hab (lt_min hδf hδg) with ⟨P, hPmesh⟩
  let tags := P.pts
  have htags : tagsInPartition P tags := by
    dsimp [tags]
    exact leftTagsInPartition P
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hPmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hPmesh (min_le_right δf δg)
  have hPf := Hf P tags htags hmeshf
  have hPg := Hg P tags htags hmeshg
  have hsum : taggedSum P tags f alpha ≤ taggedSum P tags g alpha :=
    taggedSum_mono P tags ⟨hab, hAbove, hBelow, hmono⟩ htags hfg
  have hf_bound : Lf < taggedSum P tags f alpha + eps / 2 := by
    have hleft := (abs_lt.mp hPf).1
    linarith
  have hg_bound : taggedSum P tags g alpha < Lg + eps / 2 := by
    have hright := (abs_lt.mp hPg).2
    linarith
  linarith

lemma image_const_mul_subinterval_eq_smul {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) :
    (fun x => c * f x) '' subinterval P i = c • (f '' subinterval P i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩

lemma upperStep_const_mul_nonneg {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) (hc : 0 ≤ c) :
    upperStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold upperStep
  rw [image_const_mul_subinterval_eq_smul]
  simpa [smul_eq_mul] using Real.sSup_smul_of_nonneg hc (f '' subinterval P i)

lemma lowerStep_const_mul_nonneg {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) (hc : 0 ≤ c) :
    lowerStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold lowerStep
  rw [image_const_mul_subinterval_eq_smul]
  simpa [smul_eq_mul] using Real.sInf_smul_of_nonneg hc (f '' subinterval P i)

lemma upperStep_const_mul_nonpos {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) (hc : c ≤ 0) :
    upperStep P (fun x => c * f x) i = c * lowerStep P f i := by
  unfold upperStep lowerStep
  rw [image_const_mul_subinterval_eq_smul]
  simpa [smul_eq_mul] using Real.sSup_smul_of_nonpos hc (f '' subinterval P i)

lemma lowerStep_const_mul_nonpos {a b c : ℝ} (P : Partition a b)
    (f : ℝ → ℝ) (i : ℕ) (hc : c ≤ 0) :
    lowerStep P (fun x => c * f x) i = c * upperStep P f i := by
  unfold lowerStep upperStep
  rw [image_const_mul_subinterval_eq_smul]
  simpa [smul_eq_mul] using Real.sInf_smul_of_nonpos hc (f '' subinterval P i)

theorem upperLowerCommonLimit_integrand_add {a b : ℝ} {f g alpha : ℝ → ℝ}
    {Lf Lg : ℝ}
    (hf : UpperLowerCommonLimit a b f alpha Lf)
    (hg : UpperLowerCommonLimit a b g alpha Lg) :
    UpperLowerCommonLimit a b (fun x => f x + g x) alpha (Lf + Lg) := by
  rcases hf with ⟨hsf, hlimf⟩
  rcases hg with ⟨hsg, hlimg⟩
  refine ⟨sourceHypotheses_integrand_add hsf hsg, ?_⟩
  intro eps heps
  have hhalf : 0 < eps / 2 := half_pos heps
  rcases hlimf (eps / 2) hhalf with ⟨δf, hδf, Hf⟩
  rcases hlimg (eps / 2) hhalf with ⟨δg, hδg, Hg⟩
  refine ⟨min δf δg, lt_min hδf hδg, ?_⟩
  intro P hmesh
  have hmeshf : P.mesh < δf := lt_of_lt_of_le hmesh (min_le_left δf δg)
  have hmeshg : P.mesh < δg := lt_of_lt_of_le hmesh (min_le_right δf δg)
  have hPf := Hf P hmeshf
  have hPg := Hg P hmeshg
  have hsumUpper :
      upperSum P (fun x => f x + g x) alpha ≤
        upperSum P f alpha + upperSum P g alpha :=
    upperSum_integrand_add_le P hsf hsg
  have hsumLower :
      lowerSum P f alpha + lowerSum P g alpha ≤
        lowerSum P (fun x => f x + g x) alpha :=
    lowerSum_integrand_add_le P hsf hsg
  have hlowerUpper :
      lowerSum P (fun x => f x + g x) alpha ≤
        upperSum P (fun x => f x + g x) alpha :=
    lowerSum_le_upperSum P (sourceHypotheses_integrand_add hsf hsg)
  have hlowerToUpper :
      lowerSum P f alpha + lowerSum P g alpha ≤
        upperSum P (fun x => f x + g x) alpha :=
    le_trans hsumLower hlowerUpper
  have hsumLowerToUpper :
      lowerSum P (fun x => f x + g x) alpha ≤
        upperSum P f alpha + upperSum P g alpha :=
    le_trans hlowerUpper hsumUpper
  constructor
  · apply abs_lt.mpr
    constructor
    · have hf_low : Lf - lowerSum P f alpha < eps / 2 := by
        have hle : Lf - lowerSum P f alpha ≤ |lowerSum P f alpha - Lf| := by
          linarith [neg_le_abs (lowerSum P f alpha - Lf)]
        exact lt_of_le_of_lt hle hPf.2
      have hg_low : Lg - lowerSum P g alpha < eps / 2 := by
        have hle : Lg - lowerSum P g alpha ≤ |lowerSum P g alpha - Lg| := by
          linarith [neg_le_abs (lowerSum P g alpha - Lg)]
        exact lt_of_le_of_lt hle hPg.2
      have hbound :
          (Lf + Lg) - upperSum P (fun x => f x + g x) alpha ≤
            (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) := by
        linarith
      have hlt :
          (Lf + Lg) - upperSum P (fun x => f x + g x) alpha < eps := by
        have hsum : (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) <
            eps / 2 + eps / 2 := add_lt_add hf_low hg_low
        linarith
      linarith
    · have hf_up : upperSum P f alpha - Lf < eps / 2 := by
        have hle : upperSum P f alpha - Lf ≤ |upperSum P f alpha - Lf| := le_abs_self _
        exact lt_of_le_of_lt hle hPf.1
      have hg_up : upperSum P g alpha - Lg < eps / 2 := by
        have hle : upperSum P g alpha - Lg ≤ |upperSum P g alpha - Lg| := le_abs_self _
        exact lt_of_le_of_lt hle hPg.1
      have hbound :
          upperSum P (fun x => f x + g x) alpha - (Lf + Lg) ≤
            (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) := by
        linarith
      have hlt :
          upperSum P (fun x => f x + g x) alpha - (Lf + Lg) < eps := by
        have hsum : (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) <
            eps / 2 + eps / 2 := add_lt_add hf_up hg_up
        linarith
      exact hlt
  · apply abs_lt.mpr
    constructor
    · have hf_low : Lf - lowerSum P f alpha < eps / 2 := by
        have hle : Lf - lowerSum P f alpha ≤ |lowerSum P f alpha - Lf| := by
          linarith [neg_le_abs (lowerSum P f alpha - Lf)]
        exact lt_of_le_of_lt hle hPf.2
      have hg_low : Lg - lowerSum P g alpha < eps / 2 := by
        have hle : Lg - lowerSum P g alpha ≤ |lowerSum P g alpha - Lg| := by
          linarith [neg_le_abs (lowerSum P g alpha - Lg)]
        exact lt_of_le_of_lt hle hPg.2
      have hbound :
          (Lf + Lg) - lowerSum P (fun x => f x + g x) alpha ≤
            (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) := by
        linarith
      have hlt :
          (Lf + Lg) - lowerSum P (fun x => f x + g x) alpha < eps := by
        have hsum : (Lf - lowerSum P f alpha) + (Lg - lowerSum P g alpha) <
            eps / 2 + eps / 2 := add_lt_add hf_low hg_low
        linarith
      linarith
    · have hf_up : upperSum P f alpha - Lf < eps / 2 := by
        have hle : upperSum P f alpha - Lf ≤ |upperSum P f alpha - Lf| := le_abs_self _
        exact lt_of_le_of_lt hle hPf.1
      have hg_up : upperSum P g alpha - Lg < eps / 2 := by
        have hle : upperSum P g alpha - Lg ≤ |upperSum P g alpha - Lg| := le_abs_self _
        exact lt_of_le_of_lt hle hPg.1
      have hbound :
          lowerSum P (fun x => f x + g x) alpha - (Lf + Lg) ≤
            (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) := by
        linarith
      have hlt :
          lowerSum P (fun x => f x + g x) alpha - (Lf + Lg) < eps := by
        have hsum : (upperSum P f alpha - Lf) + (upperSum P g alpha - Lg) <
            eps / 2 + eps / 2 := add_lt_add hf_up hg_up
        linarith
      exact hlt

lemma image_const_mul_Icc_eq_smul {a b c : ℝ} (f : ℝ → ℝ) :
    (fun x => c * f x) '' Icc a b = c • (f '' Icc a b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, by simp [smul_eq_mul]⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, by simp [smul_eq_mul]⟩

theorem sourceHypotheses_const_mul {a b c : ℝ} {f alpha : ℝ → ℝ}
    (h : SourceHypotheses a b f alpha) :
    SourceHypotheses a b (fun x => c * f x) alpha := by
  rcases h with ⟨hab, hAbove, hBelow, hmono⟩
  refine ⟨hab, ?_, ?_, hmono⟩
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul]
      exact hAbove.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul]
      exact BddBelow.smul_of_nonpos hc' hBelow
  · by_cases hc : 0 ≤ c
    · rw [image_const_mul_Icc_eq_smul]
      exact hBelow.smul_of_nonneg hc
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [image_const_mul_Icc_eq_smul]
      exact BddAbove.smul_of_nonpos hc' hAbove

theorem taggedSum_const_mul {a b c : ℝ} (P : Partition a b) (tags : ℕ → ℝ)
    (f alpha : ℝ → ℝ) :
    taggedSum P tags (fun x => c * f x) alpha = c * taggedSum P tags f alpha := by
  unfold taggedSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem taggedCommonLimit_const_mul {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : TaggedCommonLimit a b f alpha L) :
    TaggedCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  have hEq :
      taggedSum P tags (fun x => c * f x) alpha - c * L =
        c * (taggedSum P tags f alpha - L) := by
    rw [taggedSum_const_mul]
    ring
  rw [hEq, abs_mul]
  have hmul₁ : |c| * |taggedSum P tags f alpha - L| ≤
      |c| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt hP) (abs_nonneg c)
  have hmul₂ : |c| * (eps / C) < C * (eps / C) := by
    dsimp [C]
    exact mul_lt_mul_of_pos_right (lt_add_one |c|) hscale
  have hCmul : C * (eps / C) = eps := by
    field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)

theorem upperSum_const_mul_nonneg {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    upperSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonneg P f i hc]
  ring

theorem lowerSum_const_mul_nonneg {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : 0 ≤ c) :
    lowerSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonneg P f i hc]
  ring

theorem upperSum_const_mul_nonpos {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    upperSum P (fun x => c * f x) alpha = c * lowerSum P f alpha := by
  unfold upperSum lowerSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [upperStep_const_mul_nonpos P f i hc]
  ring

theorem lowerSum_const_mul_nonpos {a b c : ℝ} (P : Partition a b)
    (f alpha : ℝ → ℝ) (hc : c ≤ 0) :
    lowerSum P (fun x => c * f x) alpha = c * upperSum P f alpha := by
  unfold lowerSum upperSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [lowerStep_const_mul_nonpos P f i hc]
  ring

lemma abs_const_mul_error_lt {c old L eps : ℝ}
    (heps : 0 < eps) (hold : |old - L| < eps / (|c| + 1)) :
    |c * (old - L)| < eps := by
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rw [abs_mul]
  have hmul₁ : |c| * |old - L| ≤ |c| * (eps / C) :=
    mul_le_mul_of_nonneg_left (le_of_lt (by simpa [C] using hold)) (abs_nonneg c)
  have hmul₂ : |c| * (eps / C) < C * (eps / C) := by
    dsimp [C]
    exact mul_lt_mul_of_pos_right (lt_add_one |c|) hscale
  have hCmul : C * (eps / C) = eps := by
    field_simp [ne_of_gt hCpos]
  exact lt_of_le_of_lt hmul₁ (by simpa [hCmul] using hmul₂)

theorem upperLowerCommonLimit_const_mul {a b c : ℝ} {f alpha : ℝ → ℝ}
    {L : ℝ}
    (h : UpperLowerCommonLimit a b f alpha L) :
    UpperLowerCommonLimit a b (fun x => c * f x) alpha (c * L) := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_const_mul hs, ?_⟩
  intro eps heps
  let C : ℝ := |c| + 1
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [abs_nonneg c]
  have hscale : 0 < eps / C := div_pos heps hCpos
  rcases hlim (eps / C) hscale with ⟨δ, hδ, H⟩
  refine ⟨δ, hδ, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  by_cases hc : 0 ≤ c
  · constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [upperSum_const_mul_nonneg P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt heps (by simpa [C] using hP.1)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonneg P f alpha hc]
        ring
      rw [hEq]
      exact abs_const_mul_error_lt heps (by simpa [C] using hP.2)
  · have hc' : c ≤ 0 := le_of_not_ge hc
    constructor
    · have hEq :
          upperSum P (fun x => c * f x) alpha - c * L =
            c * (lowerSum P f alpha - L) := by
        rw [upperSum_const_mul_nonpos P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt heps (by simpa [C] using hP.2)
    · have hEq :
          lowerSum P (fun x => c * f x) alpha - c * L =
            c * (upperSum P f alpha - L) := by
        rw [lowerSum_const_mul_nonpos P f alpha hc']
        ring
      rw [hEq]
      exact abs_const_mul_error_lt heps (by simpa [C] using hP.1)

theorem singleJump_taggedCommonLimit {f : ℝ → ℝ} {a b c u₁ u₂ : ℝ}
    (hac : a < c) (hcb : c ≤ b) (hu : u₁ < u₂)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hcont : ContinuousAt f c) :
    TaggedCommonLimit a b f (fun x => if x < c then u₁ else u₂) (f c * (u₂ - u₁)) := by
  let jump : ℝ := u₂ - u₁
  have hjump_pos : 0 < jump := by
    dsimp [jump]
    exact sub_pos.mpr hu
  refine ⟨?_, ?_⟩
  · refine ⟨lt_of_lt_of_le hac hcb, hAbove, hBelow, ?_⟩
    exact (singleJumpStep_monotone (c := c) hu.le).monotoneOn (Icc a b)
  · intro eps heps
    let eta : ℝ := eps / (jump + 1)
    have hden_pos : 0 < jump + 1 := by positivity
    have heta_pos : 0 < eta := div_pos heps hden_pos
    rcases (Metric.continuousAt_iff.mp hcont) eta heta_pos with ⟨δ, hδ, Hδ⟩
    refine ⟨δ, hδ, ?_⟩
    intro P tags htags hmesh
    rw [singleJump_taggedSum_sub_value (P := P) (tags := tags) (f := f)
      (hac := hac) (hcb := hcb)]
    have hterm : ∀ i ∈ Finset.range P.n,
        |(f (tags i) - f c) *
          ((if P.pts (i + 1) < c then u₁ else u₂) -
            (if P.pts i < c then u₁ else u₂))| ≤
          eta * ((if P.pts (i + 1) < c then u₁ else u₂) -
            (if P.pts i < c then u₁ else u₂)) := by
      intro i hi
      let inc : ℝ := (if P.pts (i + 1) < c then u₁ else u₂) -
        (if P.pts i < c then u₁ else u₂)
      have hi_lt : i < P.n := Finset.mem_range.mp hi
      have hmono_pts : P.pts i ≤ P.pts (i + 1) := le_of_lt (P.strict_mono i hi_lt)
      have hinc_nonneg : 0 ≤ inc := by
        dsimp [inc]
        exact singleJump_increment_nonneg hu.le hmono_pts
      by_cases hinc_zero : inc = 0
      · simp [inc, hinc_zero]
      · have hcross := singleJump_increment_ne_zero_crosses hmono_pts
          (by simpa [inc] using hinc_zero)
        have htag_abs_lt : |tags i - c| < δ :=
          lt_of_le_of_lt (crossing_tag_abs_sub_le_mesh (P := P) (tags := tags)
            (i := i) hi_lt htags hcross) hmesh
        have hclose : |f (tags i) - f c| < eta := by
          have hdist : dist (tags i) c < δ := by
            simpa [Real.dist_eq] using htag_abs_lt
          simpa [Real.dist_eq] using Hδ hdist
        calc
          |(f (tags i) - f c) * inc| = |f (tags i) - f c| * inc := by
            rw [abs_mul, abs_of_nonneg hinc_nonneg]
          _ ≤ eta * inc := mul_le_mul_of_nonneg_right (le_of_lt hclose) hinc_nonneg
    calc
      |∑ i ∈ Finset.range P.n,
          ((f (tags i) - f c) *
            ((if P.pts (i + 1) < c then u₁ else u₂) -
              (if P.pts i < c then u₁ else u₂)))|
          ≤ ∑ i ∈ Finset.range P.n,
              |((f (tags i) - f c) *
                ((if P.pts (i + 1) < c then u₁ else u₂) -
                  (if P.pts i < c then u₁ else u₂)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range P.n,
              eta * ((if P.pts (i + 1) < c then u₁ else u₂) -
                (if P.pts i < c then u₁ else u₂)) := Finset.sum_le_sum hterm
      _ = eta * jump := by
        rw [← Finset.mul_sum]
        dsimp [jump]
        rw [singleJump_partition_increment_sum (P := P) (c := c)
          (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)]
      _ < eps := by
        dsimp [eta, jump]
        have hlt_ratio : (u₂ - u₁) / ((u₂ - u₁) + 1) < 1 := by
          have hden : 0 < (u₂ - u₁) + 1 := by positivity
          rw [div_lt_one hden]
          linarith [sub_pos.mpr hu]
        have hmul := mul_lt_mul_of_pos_left hlt_ratio heps
        field_simp [show (u₂ - u₁) + 1 ≠ 0 by positivity] at hmul ⊢
        nlinarith

theorem singleJump_upperLowerCommonLimit {f : ℝ → ℝ} {a b c u₁ u₂ : ℝ}
    (hac : a < c) (hcb : c ≤ b) (hu : u₁ < u₂)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hcont : ContinuousAt f c) :
    UpperLowerCommonLimit a b f (fun x => if x < c then u₁ else u₂) (f c * (u₂ - u₁)) := by
  let jump : ℝ := u₂ - u₁
  have hjump_pos : 0 < jump := by
    dsimp [jump]
    exact sub_pos.mpr hu
  refine ⟨?_, ?_⟩
  · refine ⟨lt_of_lt_of_le hac hcb, hAbove, hBelow, ?_⟩
    exact (singleJumpStep_monotone (c := c) hu.le).monotoneOn (Icc a b)
  · intro eps heps
    let eta : ℝ := eps / (jump + 1)
    have hden_pos : 0 < jump + 1 := by positivity
    have heta_pos : 0 < eta := div_pos heps hden_pos
    rcases (Metric.continuousAt_iff.mp hcont) eta heta_pos with ⟨δ, hδ, Hδ⟩
    refine ⟨δ, hδ, ?_⟩
    intro P hmesh
    have hsmall_cell : ∀ i, i < P.n →
        ((if P.pts (i + 1) < c then u₁ else u₂) -
          (if P.pts i < c then u₁ else u₂)) ≠ 0 →
        ∀ x ∈ subinterval P i, |f x - f c| < eta := by
      intro i hi hne x hx
      have hmono_pts : P.pts i ≤ P.pts (i + 1) := le_of_lt (P.strict_mono i hi)
      have hcross := singleJump_increment_ne_zero_crosses hmono_pts hne
      have hx_abs_lt : |x - c| < δ :=
        lt_of_le_of_lt (crossing_point_abs_sub_le_mesh (P := P) (i := i)
          hi hx hcross) hmesh
      have hdist : dist x c < δ := by
        simpa [Real.dist_eq] using hx_abs_lt
      simpa [Real.dist_eq] using Hδ hdist
    have hfinal_eta : eta * jump < eps := by
      dsimp [eta, jump]
      have hlt_ratio : (u₂ - u₁) / ((u₂ - u₁) + 1) < 1 := by
        have hden : 0 < (u₂ - u₁) + 1 := by positivity
        rw [div_lt_one hden]
        linarith [sub_pos.mpr hu]
      have hmul := mul_lt_mul_of_pos_left hlt_ratio heps
      field_simp [show (u₂ - u₁) + 1 ≠ 0 by positivity] at hmul ⊢
      nlinarith
    have hsum_bound_upper :
        |upperSum P f (fun x => if x < c then u₁ else u₂) - f c * (u₂ - u₁)| < eps := by
      rw [singleJump_upperSum_sub_value (P := P) (f := f) (hac := hac) (hcb := hcb)]
      have hterm : ∀ i ∈ Finset.range P.n,
          |(upperStep P f i - f c) *
            ((if P.pts (i + 1) < c then u₁ else u₂) -
              (if P.pts i < c then u₁ else u₂))| ≤
            eta * ((if P.pts (i + 1) < c then u₁ else u₂) -
              (if P.pts i < c then u₁ else u₂)) := by
        intro i hi_mem
        let inc : ℝ := (if P.pts (i + 1) < c then u₁ else u₂) -
          (if P.pts i < c then u₁ else u₂)
        have hi : i < P.n := Finset.mem_range.mp hi_mem
        have hmono_pts : P.pts i ≤ P.pts (i + 1) := le_of_lt (P.strict_mono i hi)
        have hinc_nonneg : 0 ≤ inc := by
          dsimp [inc]
          exact singleJump_increment_nonneg hu.le hmono_pts
        by_cases hzero : inc = 0
        · simp [inc, hzero]
        · have hcross := singleJump_increment_ne_zero_crosses hmono_pts
            (by simpa [inc] using hzero)
          have hupper_abs : |upperStep P f i - f c| ≤ eta :=
            upperStep_abs_sub_le_of_crossing (P := P) (i := i) hi hAbove hcross
              (hsmall_cell i hi (by simpa [inc] using hzero))
          calc
            |(upperStep P f i - f c) * inc| = |upperStep P f i - f c| * inc := by
              rw [abs_mul, abs_of_nonneg hinc_nonneg]
            _ ≤ eta * inc := mul_le_mul_of_nonneg_right hupper_abs hinc_nonneg
      calc
        |∑ i ∈ Finset.range P.n,
            ((upperStep P f i - f c) *
              ((if P.pts (i + 1) < c then u₁ else u₂) -
                (if P.pts i < c then u₁ else u₂)))|
            ≤ ∑ i ∈ Finset.range P.n,
                |((upperStep P f i - f c) *
                  ((if P.pts (i + 1) < c then u₁ else u₂) -
                    (if P.pts i < c then u₁ else u₂)))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range P.n,
                eta * ((if P.pts (i + 1) < c then u₁ else u₂) -
                  (if P.pts i < c then u₁ else u₂)) := Finset.sum_le_sum hterm
        _ = eta * jump := by
          rw [← Finset.mul_sum]
          dsimp [jump]
          rw [singleJump_partition_increment_sum (P := P) (c := c)
            (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)]
        _ < eps := hfinal_eta
    have hsum_bound_lower :
        |lowerSum P f (fun x => if x < c then u₁ else u₂) - f c * (u₂ - u₁)| < eps := by
      rw [singleJump_lowerSum_sub_value (P := P) (f := f) (hac := hac) (hcb := hcb)]
      have hterm : ∀ i ∈ Finset.range P.n,
          |(lowerStep P f i - f c) *
            ((if P.pts (i + 1) < c then u₁ else u₂) -
              (if P.pts i < c then u₁ else u₂))| ≤
            eta * ((if P.pts (i + 1) < c then u₁ else u₂) -
              (if P.pts i < c then u₁ else u₂)) := by
        intro i hi_mem
        let inc : ℝ := (if P.pts (i + 1) < c then u₁ else u₂) -
          (if P.pts i < c then u₁ else u₂)
        have hi : i < P.n := Finset.mem_range.mp hi_mem
        have hmono_pts : P.pts i ≤ P.pts (i + 1) := le_of_lt (P.strict_mono i hi)
        have hinc_nonneg : 0 ≤ inc := by
          dsimp [inc]
          exact singleJump_increment_nonneg hu.le hmono_pts
        by_cases hzero : inc = 0
        · simp [inc, hzero]
        · have hcross := singleJump_increment_ne_zero_crosses hmono_pts
            (by simpa [inc] using hzero)
          have hlower_abs : |lowerStep P f i - f c| ≤ eta :=
            lowerStep_abs_sub_le_of_crossing (P := P) (i := i) hi hBelow hcross
              (hsmall_cell i hi (by simpa [inc] using hzero))
          calc
            |(lowerStep P f i - f c) * inc| = |lowerStep P f i - f c| * inc := by
              rw [abs_mul, abs_of_nonneg hinc_nonneg]
            _ ≤ eta * inc := mul_le_mul_of_nonneg_right hlower_abs hinc_nonneg
      calc
        |∑ i ∈ Finset.range P.n,
            ((lowerStep P f i - f c) *
              ((if P.pts (i + 1) < c then u₁ else u₂) -
                (if P.pts i < c then u₁ else u₂)))|
            ≤ ∑ i ∈ Finset.range P.n,
                |((lowerStep P f i - f c) *
                  ((if P.pts (i + 1) < c then u₁ else u₂) -
                    (if P.pts i < c then u₁ else u₂)))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range P.n,
                eta * ((if P.pts (i + 1) < c then u₁ else u₂) -
                  (if P.pts i < c then u₁ else u₂)) := Finset.sum_le_sum hterm
        _ = eta * jump := by
          rw [← Finset.mul_sum]
          dsimp [jump]
          rw [singleJump_partition_increment_sum (P := P) (c := c)
            (u₁ := u₁) (u₂ := u₂) (hac := hac) (hcb := hcb)]
        _ < eps := hfinal_eta
    exact ⟨hsum_bound_upper, hsum_bound_lower⟩

lemma upperSum_congr_integrator_Icc {a b : ℝ} (P : Partition a b)
    {f α β : ℝ → ℝ}
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    upperSum P f β = upperSum P f α := by
  unfold upperSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have hleft : P.pts i ∈ Icc a b :=
    partition_pts_mem_Icc P (Nat.le_of_lt hi_lt)
  have hright : P.pts (i + 1) ∈ Icc a b :=
    partition_pts_mem_Icc P (Nat.succ_le_of_lt hi_lt)
  rw [hEq (P.pts (i + 1)) hright, hEq (P.pts i) hleft]

lemma lowerSum_congr_integrator_Icc {a b : ℝ} (P : Partition a b)
    {f α β : ℝ → ℝ}
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    lowerSum P f β = lowerSum P f α := by
  unfold lowerSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have hleft : P.pts i ∈ Icc a b :=
    partition_pts_mem_Icc P (Nat.le_of_lt hi_lt)
  have hright : P.pts (i + 1) ∈ Icc a b :=
    partition_pts_mem_Icc P (Nat.succ_le_of_lt hi_lt)
  rw [hEq (P.pts (i + 1)) hright, hEq (P.pts i) hleft]

lemma taggedSum_congr_integrator_Icc {a b : ℝ} (P : Partition a b)
    (tags : ℕ → ℝ) {f α β : ℝ → ℝ}
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    taggedSum P tags f β = taggedSum P tags f α := by
  unfold taggedSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi_lt : i < P.n := Finset.mem_range.mp hi
  have hleft : P.pts i ∈ Icc a b :=
    partition_pts_mem_Icc P (Nat.le_of_lt hi_lt)
  have hright : P.pts (i + 1) ∈ Icc a b :=
    partition_pts_mem_Icc P (Nat.succ_le_of_lt hi_lt)
  rw [hEq (P.pts (i + 1)) hright, hEq (P.pts i) hleft]

lemma sourceHypotheses_congr_integrator_Icc {a b : ℝ} {f α β : ℝ → ℝ}
    (h : SourceHypotheses a b f α)
    (hβmono : MonotoneOn β (Icc a b)) :
    SourceHypotheses a b f β := by
  rcases h with ⟨hab, hAbove, hBelow, _hαmono⟩
  exact ⟨hab, hAbove, hBelow, hβmono⟩

theorem upperLowerCommonLimit_congr_integrator_Icc {a b : ℝ} {f α β : ℝ → ℝ}
    {L : ℝ}
    (h : UpperLowerCommonLimit a b f α L)
    (hβmono : MonotoneOn β (Icc a b))
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    UpperLowerCommonLimit a b f β L := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_congr_integrator_Icc hs hβmono, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, H⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  simpa [upperSum_congr_integrator_Icc P hEq,
    lowerSum_congr_integrator_Icc P hEq] using hP

theorem taggedCommonLimit_congr_integrator_Icc {a b : ℝ} {f α β : ℝ → ℝ}
    {L : ℝ}
    (h : TaggedCommonLimit a b f α L)
    (hβmono : MonotoneOn β (Icc a b))
    (hEq : ∀ x ∈ Icc a b, β x = α x) :
    TaggedCommonLimit a b f β L := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_congr_integrator_Icc hs hβmono, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, H⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  simpa [taggedSum_congr_integrator_Icc P tags hEq] using hP

lemma upperStep_congr_integrand_Icc {a b : ℝ} (P : Partition a b)
    {f g : ℝ → ℝ} {i : ℕ} (hi : i < P.n)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    upperStep P g i = upperStep P f i := by
  have himage : g '' subinterval P i = f '' subinterval P i := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x (subinterval_subset_Icc P hi hx)]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x (subinterval_subset_Icc P hi hx)]⟩
  unfold upperStep
  rw [himage]

lemma lowerStep_congr_integrand_Icc {a b : ℝ} (P : Partition a b)
    {f g : ℝ → ℝ} {i : ℕ} (hi : i < P.n)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    lowerStep P g i = lowerStep P f i := by
  have himage : g '' subinterval P i = f '' subinterval P i := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x (subinterval_subset_Icc P hi hx)]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x (subinterval_subset_Icc P hi hx)]⟩
  unfold lowerStep
  rw [himage]

lemma upperSum_congr_integrand_Icc {a b : ℝ} (P : Partition a b)
    {f g α : ℝ → ℝ} (hEq : ∀ x ∈ Icc a b, g x = f x) :
    upperSum P g α = upperSum P f α := by
  unfold upperSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < P.n := Finset.mem_range.mp hi
  rw [upperStep_congr_integrand_Icc P hi' hEq]

lemma lowerSum_congr_integrand_Icc {a b : ℝ} (P : Partition a b)
    {f g α : ℝ → ℝ} (hEq : ∀ x ∈ Icc a b, g x = f x) :
    lowerSum P g α = lowerSum P f α := by
  unfold lowerSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < P.n := Finset.mem_range.mp hi
  rw [lowerStep_congr_integrand_Icc P hi' hEq]

lemma taggedSum_congr_integrand_Icc {a b : ℝ} (P : Partition a b)
    (tags : ℕ → ℝ) {f g α : ℝ → ℝ}
    (htags : tagsInPartition P tags)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    taggedSum P tags g α = taggedSum P tags f α := by
  unfold taggedSum
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < P.n := Finset.mem_range.mp hi
  have htag : tags i ∈ Icc a b := subinterval_subset_Icc P hi' (htags i hi')
  rw [hEq (tags i) htag]

lemma sourceHypotheses_congr_integrand_Icc {a b : ℝ} {f g α : ℝ → ℝ}
    (h : SourceHypotheses a b f α)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    SourceHypotheses a b g α := by
  rcases h with ⟨hab, hAbove, hBelow, hmono⟩
  have himage : g '' Icc a b = f '' Icc a b := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x hx]⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by rw [hEq x hx]⟩
  exact ⟨hab, by simpa [himage] using hAbove, by simpa [himage] using hBelow, hmono⟩

theorem upperLowerCommonLimit_congr_integrand_Icc {a b : ℝ} {f g α : ℝ → ℝ}
    {L : ℝ}
    (h : UpperLowerCommonLimit a b f α L)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    UpperLowerCommonLimit a b g α L := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_congr_integrand_Icc hs hEq, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, H⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P hmesh
  have hP := H P hmesh
  simpa [upperSum_congr_integrand_Icc P hEq,
    lowerSum_congr_integrand_Icc P hEq] using hP

theorem taggedCommonLimit_congr_integrand_Icc {a b : ℝ} {f g α : ℝ → ℝ}
    {L : ℝ}
    (h : TaggedCommonLimit a b f α L)
    (hEq : ∀ x ∈ Icc a b, g x = f x) :
    TaggedCommonLimit a b g α L := by
  rcases h with ⟨hs, hlim⟩
  refine ⟨sourceHypotheses_congr_integrand_Icc hs hEq, ?_⟩
  intro eps heps
  rcases hlim eps heps with ⟨delta, hdelta, H⟩
  refine ⟨delta, hdelta, ?_⟩
  intro P tags htags hmesh
  have hP := H P tags htags hmesh
  simpa [taggedSum_congr_integrand_Icc P tags htags hEq] using hP

end DarbouxRS
