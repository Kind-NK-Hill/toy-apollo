/-
TASK ID: prob_11_10
TYPE: Problem
SOURCE PLAN: chapter11-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.ex_11_5_1
import ToyApollo.Output.thm_11_6

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

noncomputable section

def prob_11_10_continuousCDF (F : ℝ → ℝ) : Prop :=
  Monotone F ∧ Continuous F ∧ Tendsto F atBot (nhds 0) ∧ Tendsto F atTop (nhds 1)

noncomputable def prob_11_10_uniformCDFDeviation {Ω : Type*}
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => sSup (Set.range fun x : ℝ => |empiricalCDFAt X x n ω - F x|)

def prob_11_10_pointwiseIndicatorAssumptions {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x : ℝ,
    Integrable (empiricalCDFIndicator X x 0) P ∧
      (Pairwise fun i j =>
        empiricalCDFIndicator X x i ⟂ᵢ[P] empiricalCDFIndicator X x j) ∧
      (∀ i, IdentDistrib
        (empiricalCDFIndicator X x i) (empiricalCDFIndicator X x 0) P P) ∧
      P[empiricalCDFIndicator X x 0] = F x

lemma prob_11_10_continuousCDF_bounds (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F) (x : ℝ) :
    0 ≤ F x ∧ F x ≤ 1 := by
  rcases hCDF with ⟨hmono, _hcont, hbot, htop⟩
  exact ⟨hmono.le_of_tendsto hbot x, hmono.ge_of_tendsto htop x⟩

lemma prob_11_10_continuousCDF_tail_cutoffs (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F) {η : ℝ} (hη : 0 < η) :
    ∃ A B : ℝ, A ≤ B ∧ F A < η ∧ 1 - F B < η := by
  rcases hCDF with ⟨hmono, _hcont, hbot, htop⟩
  have hleft_event : ∀ᶠ x in atBot, F x < η :=
    hbot.eventually (eventually_lt_nhds hη)
  rcases eventually_atBot.1 hleft_event with ⟨A₀, hA₀⟩
  have hright_nhds : ∀ᶠ y in nhds (1 : ℝ), 1 - y < η := by
    filter_upwards [eventually_gt_nhds (by linarith : 1 - η < (1 : ℝ))] with y hy
    linarith
  have hright_event : ∀ᶠ x in atTop, 1 - F x < η :=
    htop.eventually hright_nhds
  rcases eventually_atTop.1 hright_event with ⟨B₀, hB₀⟩
  refine ⟨min A₀ B₀, max A₀ B₀, le_max_of_le_left (min_le_left A₀ B₀), ?_, ?_⟩
  · exact lt_of_le_of_lt (hmono (min_le_left A₀ B₀)) (hA₀ A₀ le_rfl)
  · have hB₀_le : B₀ ≤ max A₀ B₀ := le_max_right A₀ B₀
    have hF_le : 1 - F (max A₀ B₀) ≤ 1 - F B₀ := by
      linarith [hmono hB₀_le]
    exact lt_of_le_of_lt hF_le (hB₀ B₀ le_rfl)

lemma prob_11_10_uniformCDFDeviation_le_of_pointwise {Ω : Type*}
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) (n : ℕ) (ω : Ω) (B : ℝ)
    (hpoint : ∀ x : ℝ, |empiricalCDFAt X x n ω - F x| ≤ B) :
    prob_11_10_uniformCDFDeviation X F n ω ≤ B := by
  unfold prob_11_10_uniformCDFDeviation
  refine csSup_le (Set.range_nonempty _) ?_
  rintro y ⟨x, rfl⟩
  exact hpoint x

lemma prob_11_10_continuousCDF_finite_grid {F : ℝ → ℝ}
    (hCDF : prob_11_10_continuousCDF F) {η : ℝ} (hη : 0 < η) :
    ∃ A B : ℝ, ∃ grid : Finset ℝ,
      A ≤ B ∧ A ∈ grid ∧ B ∈ grid ∧ F A < η ∧ 1 - F B < η ∧
        ∀ x : ℝ, A ≤ x → x ≤ B →
          ∃ a ∈ grid, ∃ b ∈ grid, a ≤ x ∧ x ≤ b ∧ F b - F a < η := by
  classical
  rcases hCDF with ⟨hmono, hcont, hbot, htop⟩
  obtain ⟨A, B, hAB, hA_tail, hB_tail⟩ :=
    prob_11_10_continuousCDF_tail_cutoffs F ⟨hmono, hcont, hbot, htop⟩ hη
  have hη3 : 0 < η := hη
  have hcompact : IsCompact (Set.Icc (A - 1) (B + 1)) := isCompact_Icc
  have huc :
      UniformContinuousOn F (Set.Icc (A - 1) (B + 1)) :=
    hcompact.uniformContinuousOn_of_continuous hcont.continuousOn
  rcases (Metric.uniformContinuousOn_iff.mp huc) η hη3 with ⟨δ, hδpos, hδ⟩
  let ρ : ℝ := min (δ / 3) (1 / 2)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (by norm_num)
  have hρ_le_delta : ρ ≤ δ / 3 := min_le_left _ _
  have hρ_le_one : ρ ≤ 1 := by
    have hρ_le_half : ρ ≤ (1 / 2 : ℝ) := min_le_right _ _
    linarith
  rcases finite_cover_balls_of_compact (s := Set.Icc A B) isCompact_Icc hρpos with
    ⟨centers, hcenters_subset, hcenters_fin, hcover⟩
  let centerFinset : Finset ℝ := hcenters_fin.toFinset
  let grid : Finset ℝ :=
    ({A, B} : Finset ℝ) ∪
      (centerFinset.image fun c : ℝ => c - ρ) ∪
        (centerFinset.image fun c : ℝ => c + ρ)
  have hA_grid : A ∈ grid := by
    dsimp [grid]
    exact Finset.mem_union.2
      (Or.inl (Finset.mem_union.2 (Or.inl (by simp))))
  have hB_grid : B ∈ grid := by
    dsimp [grid]
    exact Finset.mem_union.2
      (Or.inl (Finset.mem_union.2 (Or.inl (by simp))))
  refine ⟨A, B, grid, hAB, hA_grid, hB_grid, hA_tail, hB_tail, ?_⟩
  intro x hAx hxB
  have hxIcc : x ∈ Set.Icc A B := ⟨hAx, hxB⟩
  have hxcover : x ∈ ⋃ c ∈ centers, Metric.ball c ρ := hcover hxIcc
  simp only [Set.mem_iUnion] at hxcover
  rcases hxcover with ⟨c, hc⟩
  rcases hc with ⟨hc_centers, hxc_ball⟩
  have hcIcc : c ∈ Set.Icc A B := hcenters_subset hc_centers
  have hc_fin : c ∈ centerFinset := by
    simpa [centerFinset] using hcenters_fin.mem_toFinset.mpr hc_centers
  let a : ℝ := c - ρ
  let b : ℝ := c + ρ
  have ha_image : a ∈ centerFinset.image (fun c : ℝ => c - ρ) := by
    exact Finset.mem_image.2 ⟨c, hc_fin, rfl⟩
  have hb_image : b ∈ centerFinset.image (fun c : ℝ => c + ρ) := by
    exact Finset.mem_image.2 ⟨c, hc_fin, rfl⟩
  have ha_grid : a ∈ grid := by
    dsimp [grid]
    exact Finset.mem_union.2
      (Or.inl (Finset.mem_union.2 (Or.inr ha_image)))
  have hb_grid : b ∈ grid := by
    dsimp [grid]
    exact Finset.mem_union.2 (Or.inr hb_image)
  have hdist : dist x c < ρ := by
    simpa [Metric.mem_ball] using hxc_ball
  have hax : a ≤ x := by
    rw [Real.dist_eq] at hdist
    have hlt := (abs_lt.mp hdist).1
    dsimp [a]
    linarith
  have hxb : x ≤ b := by
    rw [Real.dist_eq] at hdist
    have hlt := (abs_lt.mp hdist).2
    dsimp [b]
    linarith
  have ha_mem : a ∈ Set.Icc (A - 1) (B + 1) := by
    rcases hcIcc with ⟨hAc, hcB⟩
    dsimp [a]
    constructor <;> linarith
  have hb_mem : b ∈ Set.Icc (A - 1) (B + 1) := by
    rcases hcIcc with ⟨hAc, hcB⟩
    dsimp [b]
    constructor <;> linarith
  have hab_dist : dist a b < δ := by
    rw [Real.dist_eq]
    dsimp [a, b, ρ] at *
    have hδnonneg : 0 ≤ δ := le_of_lt hδpos
    have hρ_nonneg : 0 ≤ min (δ / 3) (1 / 2 : ℝ) := le_of_lt hρpos
    have habs : |(c - min (δ / 3) (1 / 2 : ℝ)) -
        (c + min (δ / 3) (1 / 2 : ℝ))| =
        2 * min (δ / 3) (1 / 2 : ℝ) := by
      rw [show (c - min (δ / 3) (1 / 2 : ℝ)) -
          (c + min (δ / 3) (1 / 2 : ℝ)) =
          -(2 * min (δ / 3) (1 / 2 : ℝ)) by ring]
      rw [abs_neg, abs_of_nonneg (mul_nonneg (by norm_num) hρ_nonneg)]
    rw [habs]
    nlinarith [hρ_le_delta]
  have hFdist : dist (F a) (F b) < η := hδ a ha_mem b hb_mem hab_dist
  have hab_order : a ≤ b := by
    dsimp [a, b]
    linarith
  have hFmono_ab : F a ≤ F b := hmono hab_order
  have hFgap : F b - F a < η := by
    rw [Real.dist_eq] at hFdist
    have habs : |F a - F b| = F b - F a := by
      rw [abs_of_nonpos (sub_nonpos.mpr hFmono_ab)]
      ring
    linarith
  exact ⟨a, ha_grid, b, hb_grid, hax, hxb, hFgap⟩

lemma prob_11_10_finite_grid_pointwise_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) (grid : Finset ℝ)
    (hPointwise :
      ∀ x : ℝ,
        ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x)) :
    ∀ᵐ ω ∂P, ∀ x ∈ grid,
      Tendsto (fun n : ℕ => empiricalCDFAt X x n ω) atTop (nhds (F x)) := by
  classical
  refine Finset.induction_on grid ?empty ?insert
  · simp
  · intro a s has hs
    filter_upwards [(hPointwise a).2.2, hs] with ω ha hsω x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact hsω x hx

lemma prob_11_10_empiricalCDFIndicator_mono {Ω : Type*}
    (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) :
    Monotone (fun x : ℝ => empiricalCDFIndicator X x k ω) := by
  intro x y hxy
  unfold empiricalCDFIndicator
  by_cases hx : X k ω ≤ x
  · have hy : X k ω ≤ y := le_trans hx hxy
    simp [hx, hy]
  · by_cases hy : X k ω ≤ y
    · simp [hx, hy]
    · simp [hx, hy]

lemma prob_11_10_empiricalCDFAt_mono {Ω : Type*}
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Monotone (fun x : ℝ => empiricalCDFAt X x n ω) := by
  intro x y hxy
  unfold empiricalCDFAt thm_11_5_sampleMean
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · exact Finset.sum_le_sum
      (fun i _ => prob_11_10_empiricalCDFIndicator_mono X i.1 ω hxy)
  · positivity

lemma prob_11_10_empiricalCDFIndicator_nonneg {Ω : Type*}
    (X : ℕ → Ω → ℝ) (x : ℝ) (k : ℕ) (ω : Ω) :
    0 ≤ empiricalCDFIndicator X x k ω := by
  unfold empiricalCDFIndicator
  split <;> norm_num

lemma prob_11_10_empiricalCDFIndicator_le_one {Ω : Type*}
    (X : ℕ → Ω → ℝ) (x : ℝ) (k : ℕ) (ω : Ω) :
    empiricalCDFIndicator X x k ω ≤ 1 := by
  unfold empiricalCDFIndicator
  split <;> norm_num

lemma prob_11_10_empiricalCDFAt_nonneg {Ω : Type*}
    (X : ℕ → Ω → ℝ) (x : ℝ) (n : ℕ) (ω : Ω) :
    0 ≤ empiricalCDFAt X x n ω := by
  unfold empiricalCDFAt thm_11_5_sampleMean
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg
      (fun i _ => prob_11_10_empiricalCDFIndicator_nonneg X x i.1 ω))

lemma prob_11_10_empiricalCDFAt_le_one {Ω : Type*}
    (X : ℕ → Ω → ℝ) (x : ℝ) (n : ℕ) (ω : Ω) :
    empiricalCDFAt X x n ω ≤ 1 := by
  unfold empiricalCDFAt thm_11_5_sampleMean
  have hsum :
      (∑ i : Fin (n + 1), empiricalCDFIndicator X x i.1 ω) ≤ (n + 1 : ℝ) := by
    calc
      (∑ i : Fin (n + 1), empiricalCDFIndicator X x i.1 ω)
          ≤ ∑ _i : Fin (n + 1), (1 : ℝ) := by
            exact Finset.sum_le_sum
              (fun i _ => prob_11_10_empiricalCDFIndicator_le_one X x i.1 ω)
      _ = (n + 1 : ℝ) := by simp
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 1 / ((n : ℝ) + 1) by positivity)
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  have hone : (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) = 1 := by
    field_simp [hden]
  nlinarith

lemma prob_11_10_pathwise_grid_sandwich {Ω : Type*}
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) (hCDF : prob_11_10_continuousCDF F)
    {η A B : ℝ} {grid : Finset ℝ} {n : ℕ} {ω : Ω}
    (hη : 0 < η) (_hAB : A ≤ B) (hA_grid : A ∈ grid) (hB_grid : B ∈ grid)
    (hA_tail : F A < η) (hB_tail : 1 - F B < η)
    (hgrid :
      ∀ x : ℝ, A ≤ x → x ≤ B →
        ∃ a ∈ grid, ∃ b ∈ grid, a ≤ x ∧ x ≤ b ∧ F b - F a < η)
    (hgrid_close :
      ∀ y ∈ grid, |empiricalCDFAt X y n ω - F y| < η) :
    ∀ x : ℝ, |empiricalCDFAt X x n ω - F x| < 2 * η := by
  intro x
  rcases hCDF with ⟨hFmono, _hFcont, hFbot, hFtop⟩
  have hE_mono : Monotone (fun y : ℝ => empiricalCDFAt X y n ω) :=
    prob_11_10_empiricalCDFAt_mono X n ω
  have hF_bounds :
      ∀ y : ℝ, 0 ≤ F y ∧ F y ≤ 1 :=
    prob_11_10_continuousCDF_bounds F ⟨hFmono, _hFcont, hFbot, hFtop⟩
  by_cases hx_left : x < A
  · have hFx_small : F x < η := lt_of_le_of_lt (hFmono hx_left.le) hA_tail
    have hEx_nonneg : 0 ≤ empiricalCDFAt X x n ω :=
      prob_11_10_empiricalCDFAt_nonneg X x n ω
    have hFx_nonneg : 0 ≤ F x := (hF_bounds x).1
    have hEx_le_EA : empiricalCDFAt X x n ω ≤ empiricalCDFAt X A n ω :=
      hE_mono hx_left.le
    have hEA_close := hgrid_close A hA_grid
    have hEA_upper : empiricalCDFAt X A n ω < F A + η := by
      have := (abs_lt.mp hEA_close).2
      linarith
    have hEA_small : empiricalCDFAt X A n ω < 2 * η := by
      linarith
    rw [abs_lt]
    constructor <;> linarith
  · by_cases hx_right : B < x
    · have hFx_large : F B ≤ F x := hFmono hx_right.le
      have hFx_le_one : F x ≤ 1 := (hF_bounds x).2
      have hEx_le_one : empiricalCDFAt X x n ω ≤ 1 :=
        prob_11_10_empiricalCDFAt_le_one X x n ω
      have hEx_ge_EB : empiricalCDFAt X B n ω ≤ empiricalCDFAt X x n ω :=
        hE_mono hx_right.le
      have hEB_close := hgrid_close B hB_grid
      have hEB_lower : F B - η < empiricalCDFAt X B n ω := by
        have := (abs_lt.mp hEB_close).1
        linarith
      rw [abs_lt]
      constructor <;> linarith
    · have hAx : A ≤ x := le_of_not_gt hx_left
      have hxB : x ≤ B := le_of_not_gt hx_right
      rcases hgrid x hAx hxB with
        ⟨a, ha_grid, b, hb_grid, hax, hxb, hFgap⟩
      have hEa_le_Ex : empiricalCDFAt X a n ω ≤ empiricalCDFAt X x n ω :=
        hE_mono hax
      have hEx_le_Eb : empiricalCDFAt X x n ω ≤ empiricalCDFAt X b n ω :=
        hE_mono hxb
      have hFa_le_Fx : F a ≤ F x := hFmono hax
      have hFx_le_Fb : F x ≤ F b := hFmono hxb
      have ha_close := hgrid_close a ha_grid
      have hb_close := hgrid_close b hb_grid
      have hEa_lower : F a - η < empiricalCDFAt X a n ω := by
        have := (abs_lt.mp ha_close).1
        linarith
      have hEb_upper : empiricalCDFAt X b n ω < F b + η := by
        have := (abs_lt.mp hb_close).2
        linarith
      rw [abs_lt]
      constructor <;> linarith

lemma prob_11_10_uniformCDFDeviation_nonneg {Ω : Type*}
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) (hCDF : prob_11_10_continuousCDF F)
    (n : ℕ) (ω : Ω) :
    0 ≤ prob_11_10_uniformCDFDeviation X F n ω := by
  unfold prob_11_10_uniformCDFDeviation
  have hbdd :
      BddAbove
        (Set.range fun x : ℝ => |empiricalCDFAt X x n ω - F x|) := by
    refine ⟨1, ?_⟩
    rintro y ⟨x, rfl⟩
    have hE0 := prob_11_10_empiricalCDFAt_nonneg X x n ω
    have hE1 := prob_11_10_empiricalCDFAt_le_one X x n ω
    have hF0 := (prob_11_10_continuousCDF_bounds F hCDF x).1
    have hF1 := (prob_11_10_continuousCDF_bounds F hCDF x).2
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hmem :
      |empiricalCDFAt X 0 n ω - F 0| ∈
        Set.range fun x : ℝ => |empiricalCDFAt X x n ω - F x| :=
    ⟨0, rfl⟩
  exact (abs_nonneg _).trans (le_csSup hbdd hmem)

lemma prob_11_10_empiricalCDFIndicator_continuousWithinAt_Ici {Ω : Type*}
    (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ => empiricalCDFIndicator X y k ω)
      (Set.Ici x) x := by
  by_cases hk : X k ω ≤ x
  · have heq :
        (fun y : ℝ => empiricalCDFIndicator X y k ω) =ᶠ[𝓝[Set.Ici x] x]
          (fun _ : ℝ => (1 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      simp [empiricalCDFIndicator, le_trans hk hy]
    exact
      (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : ℝ => (1 : ℝ)) (Set.Ici x) x
      ).congr_of_eventuallyEq heq (by simp [empiricalCDFIndicator, hk])
  · have hxk : x < X k ω := lt_of_not_ge hk
    have heq :
        (fun y : ℝ => empiricalCDFIndicator X y k ω) =ᶠ[𝓝[Set.Ici x] x]
          (fun _ : ℝ => 0) := by
      apply mem_nhdsWithin_of_mem_nhds
      filter_upwards [Iio_mem_nhds hxk] with y hy
      have hy' : y < X k ω := by
        simpa only [Set.mem_Iio] using hy
      simp [empiricalCDFIndicator, hy']
    exact
      (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Set.Ici x) x
      ).congr_of_eventuallyEq heq (by simp [empiricalCDFIndicator, hk])

lemma prob_11_10_empiricalCDFAt_continuousWithinAt_Ici {Ω : Type*}
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) :
    ContinuousWithinAt (fun y : ℝ => empiricalCDFAt X y n ω)
      (Set.Ici x) x := by
  unfold empiricalCDFAt thm_11_5_sampleMean
  have hsum :
      ContinuousWithinAt
        (fun y : ℝ => ∑ i : Fin (n + 1), empiricalCDFIndicator X y i.1 ω)
        (Set.Ici x) x := by
    change Tendsto
      (fun y : ℝ => ∑ i : Fin (n + 1), empiricalCDFIndicator X y i.1 ω)
      (𝓝[Set.Ici x] x)
      (𝓝 (∑ i : Fin (n + 1), empiricalCDFIndicator X x i.1 ω))
    simpa using
      (tendsto_finsetSum (Finset.univ : Finset (Fin (n + 1)))
        (fun i _ =>
          (prob_11_10_empiricalCDFIndicator_continuousWithinAt_Ici
            X i.1 ω x).tendsto))
  change ContinuousWithinAt
    ((fun _ : ℝ => 1 / ((n : ℝ) + 1)) *
      (fun y : ℝ => ∑ i : Fin (n + 1), empiricalCDFIndicator X y i.1 ω))
    (Set.Ici x) x
  exact continuousWithinAt_const.mul hsum

lemma prob_11_10_empiricalCDFError_continuousWithinAt_Ici {Ω : Type*}
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F) (n : ℕ) (ω : Ω) (x : ℝ) :
    ContinuousWithinAt
      (fun y : ℝ => |empiricalCDFAt X y n ω - F y|) (Set.Ici x) x := by
  exact ((prob_11_10_empiricalCDFAt_continuousWithinAt_Ici X n ω x).sub
    hCDF.2.1.continuousAt.continuousWithinAt).abs

lemma prob_11_10_empiricalCDFError_le_one {Ω : Type*}
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F) (n : ℕ) (ω : Ω) (x : ℝ) :
    |empiricalCDFAt X x n ω - F x| ≤ 1 := by
  have hE0 := prob_11_10_empiricalCDFAt_nonneg X x n ω
  have hE1 := prob_11_10_empiricalCDFAt_le_one X x n ω
  have hF0 := (prob_11_10_continuousCDF_bounds F hCDF x).1
  have hF1 := (prob_11_10_continuousCDF_bounds F hCDF x).2
  rw [abs_sub_le_iff]
  constructor <;> linarith

lemma prob_11_10_uniformCDFDeviation_eq_iSup_rat {Ω : Type*}
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F) (n : ℕ) (ω : Ω) :
    prob_11_10_uniformCDFDeviation X F n ω =
      ⨆ q : ℚ, |empiricalCDFAt X (q : ℝ) n ω - F (q : ℝ)| := by
  unfold prob_11_10_uniformCDFDeviation
  rw [sSup_range]
  have hbdd_real :
      BddAbove
        (Set.range fun x : ℝ => |empiricalCDFAt X x n ω - F x|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact prob_11_10_empiricalCDFError_le_one X F hCDF n ω x
  have hbdd_rat :
      BddAbove
        (Set.range fun q : ℚ =>
          |empiricalCDFAt X (q : ℝ) n ω - F (q : ℝ)|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact prob_11_10_empiricalCDFError_le_one X F hCDF n ω (q : ℝ)
  apply le_antisymm
  · refine ciSup_le fun x => ?_
    let q : ℕ → ℚ := fun m =>
      Classical.choose
        (exists_rat_btwn (K := ℝ)
          (show x < x + 1 / ((m : ℝ) + 1) by
            have hm : 0 < 1 / ((m : ℝ) + 1) := by positivity
            linarith))
    have hq_spec (m : ℕ) :
        x < (q m : ℝ) ∧ (q m : ℝ) < x + 1 / ((m : ℝ) + 1) :=
      Classical.choose_spec
        (exists_rat_btwn (K := ℝ)
          (show x < x + 1 / ((m : ℝ) + 1) by
            have hm : 0 < 1 / ((m : ℝ) + 1) := by positivity
            linarith))
    have hq_sub :
        Tendsto (fun m : ℕ => (q m : ℝ) - x) atTop (𝓝 0) := by
      exact squeeze_zero
        (fun m => sub_nonneg.mpr (hq_spec m).1.le)
        (fun m => by linarith [(hq_spec m).2])
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hq_tendsto : Tendsto (fun m : ℕ => (q m : ℝ)) atTop (𝓝 x) := by
      have hconst : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) :=
        tendsto_const_nhds
      simpa only [add_sub_cancel, add_zero] using hconst.add hq_sub
    have hq_within :
        Tendsto (fun m : ℕ => (q m : ℝ)) atTop (𝓝[Set.Ici x] x) := by
      exact tendsto_nhdsWithin_iff.mpr
        ⟨hq_tendsto, Filter.Eventually.of_forall
          (fun m => (hq_spec m).1.le)⟩
    have herr_tendsto :
        Tendsto
          (fun m : ℕ =>
            |empiricalCDFAt X (q m : ℝ) n ω - F (q m : ℝ)|)
          atTop (𝓝 |empiricalCDFAt X x n ω - F x|) :=
      (prob_11_10_empiricalCDFError_continuousWithinAt_Ici
        X F hCDF n ω x).tendsto.comp hq_within
    exact le_of_tendsto' herr_tendsto
      (fun m => le_ciSup hbdd_rat (q m))
  · exact ciSup_le fun q => le_ciSup hbdd_real (q : ℝ)

theorem prob_11_10_uniformCDFDeviation_aestronglyMeasurable {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F)
    (hPointwise :
      ∀ x : ℝ,
        ConvergesAlmostSurely P
          (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x))
    (n : ℕ) :
    AEStronglyMeasurable (prob_11_10_uniformCDFDeviation X F n) P := by
  have hrat :
      ∀ q : ℚ,
        AEMeasurable
          (fun ω => |empiricalCDFAt X (q : ℝ) n ω - F (q : ℝ)|) P := by
    intro q
    exact (((hPointwise (q : ℝ)).1 n).aemeasurable.sub aemeasurable_const).abs
  have hiSup :
      AEStronglyMeasurable
        (fun ω =>
          ⨆ q : ℚ, |empiricalCDFAt X (q : ℝ) n ω - F (q : ℝ)|) P :=
    (AEMeasurable.iSup hrat).aestronglyMeasurable
  exact hiSup.congr
    (Filter.Eventually.of_forall fun ω =>
      (prob_11_10_uniformCDFDeviation_eq_iSup_rat X F hCDF n ω).symm)

theorem prob_11_10_polya_uniformization_from_pointwise {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F)
    (_hIndicators : prob_11_10_pointwiseIndicatorAssumptions P X F)
    (hPointwise :
      ∀ x : ℝ,
        ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x)) :
    ConvergesAlmostSurely P
      (fun n => prob_11_10_uniformCDFDeviation X F n) (fun _ : Ω => 0) := by
  refine ⟨fun n =>
    prob_11_10_uniformCDFDeviation_aestronglyMeasurable
      P X F hCDF hPointwise n, aestronglyMeasurable_const, ?_⟩
  have hAll : ∀ᵐ ω ∂P, ∀ m : ℕ,
      ∀ᶠ n : ℕ in atTop,
        dist (prob_11_10_uniformCDFDeviation X F n ω) 0 <
          1 / ((m : ℝ) + 1) := by
    refine ae_all_iff.mpr ?_
    intro m
    let ε : ℝ := 1 / ((m : ℝ) + 1)
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    let η : ℝ := ε / 3
    have hη : 0 < η := by
      dsimp [η]
      positivity
    obtain ⟨A, B, grid, hAB, hA_grid, hB_grid, hA_tail, hB_tail, hgrid⟩ :=
      prob_11_10_continuousCDF_finite_grid hCDF hη
    have hgrid_ae :
        ∀ᵐ ω ∂P, ∀ x ∈ grid,
          Tendsto (fun n : ℕ => empiricalCDFAt X x n ω) atTop (nhds (F x)) :=
      prob_11_10_finite_grid_pointwise_ae P X F grid hPointwise
    filter_upwards [hgrid_ae] with ω hω
    have hclose_event :
        ∀ᶠ n : ℕ in atTop, ∀ y ∈ grid,
          |empiricalCDFAt X y n ω - F y| < η := by
      rw [Filter.eventually_all_finset]
      intro y hy
      have hy_tendsto := hω y hy
      have hy_event :
          ∀ᶠ n : ℕ in atTop,
            dist (empiricalCDFAt X y n ω) (F y) < η :=
        hy_tendsto.eventually (Metric.ball_mem_nhds (F y) hη)
      simpa [Real.dist_eq] using hy_event
    filter_upwards [hclose_event] with n hclose
    have hpath :
        ∀ x : ℝ, |empiricalCDFAt X x n ω - F x| < 2 * η :=
      prob_11_10_pathwise_grid_sandwich X F hCDF hη hAB hA_grid hB_grid
        hA_tail hB_tail hgrid hclose
    have hdev_le :
        prob_11_10_uniformCDFDeviation X F n ω ≤ 2 * η :=
      prob_11_10_uniformCDFDeviation_le_of_pointwise X F n ω (2 * η)
        (fun x => le_of_lt (hpath x))
    have hdev_nonneg :
        0 ≤ prob_11_10_uniformCDFDeviation X F n ω :=
      prob_11_10_uniformCDFDeviation_nonneg X F hCDF n ω
    have htwo_eta : 2 * η < ε := by
      dsimp [η]
      linarith
    rw [Real.dist_eq]
    have habs :
        |prob_11_10_uniformCDFDeviation X F n ω - 0| =
          prob_11_10_uniformCDFDeviation X F n ω := by
      rw [sub_zero, abs_of_nonneg hdev_nonneg]
    rw [habs]
    exact lt_of_le_of_lt hdev_le htwo_eta
  filter_upwards [hAll] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 1 / ((m : ℝ) + 1) < ε := by
    simpa using (exists_nat_one_div_lt hε)
  rcases Filter.eventually_atTop.mp (hω m) with ⟨N, hN⟩
  exact ⟨N, fun n hn => lt_trans (hN n hn) hm⟩

theorem prob_11_10_finite_grid_uniformization {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F)
    (hIndicators : prob_11_10_pointwiseIndicatorAssumptions P X F)
    (hPointwise :
      ∀ x : ℝ,
        ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x)) :
    ConvergesAlmostSurely P
      (fun n => prob_11_10_uniformCDFDeviation X F n) (fun _ : Ω => 0) := by
  exact prob_11_10_polya_uniformization_from_pointwise P X F hCDF hIndicators
    hPointwise

theorem prob_11_10_continuous_grid_uniformization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F)
    (hIndicators : prob_11_10_pointwiseIndicatorAssumptions P X F)
    (hPointwise :
      ∀ x : ℝ,
        ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x)) :
    ConvergesAlmostSurely P
      (fun n => prob_11_10_uniformCDFDeviation X F n) (fun _ : Ω => 0) := by
  exact prob_11_10_finite_grid_uniformization P X F hCDF hIndicators
    hPointwise

theorem prob_11_10_pointwise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hIndicators : prob_11_10_pointwiseIndicatorAssumptions P X F) (x : ℝ) :
    ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x) := by
  rcases hIndicators x with ⟨hInt, hPairwise, hIdent, hMean⟩
  exact ex_11_5_1 P X F x hInt hPairwise hIdent hMean

theorem prob_11_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F)
    (hIndicators : prob_11_10_pointwiseIndicatorAssumptions P X F) :
    ConvergesAlmostSurely P
      (fun n => prob_11_10_uniformCDFDeviation X F n) (fun _ : Ω => 0) := by
  exact prob_11_10_continuous_grid_uniformization P X F
    hCDF hIndicators
      (fun x => prob_11_10_pointwise P X F hIndicators x)
