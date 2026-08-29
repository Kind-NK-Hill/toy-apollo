/-
TASK ID: thm_12_3
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter12-l2-norm-inner-product
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_7_3
import ToyApollo.Output.prob_7_7
import ToyApollo.Output.def_12_2
import ToyApollo.Output.def_12_3
import ToyApollo.Output.thm_12_1
import ToyApollo.Output.thm_12_2

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

theorem thm_12_3_fatou_input {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ENNReal) (hX : ∀ n, Measurable (X n)) :
    ∫⁻ ω, Filter.liminf (fun n => X n ω) Filter.atTop ∂P ≤
      Filter.liminf (fun n => ∫⁻ ω, X n ω ∂P) Filter.atTop :=
  thm_7_3 P X hX

theorem thm_12_3_series_ae_limit_input {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ) (hf : ∀ k, Measurable (f k))
    (h : HasFiniteAbsIntegralSeries P f) :
    ∀ᵐ ω ∂P, ∃ L : ℝ,
      Tendsto (fun n => ∑ k ∈ Finset.range n, f k ω) atTop (𝓝 L) :=
  (prob_7_7 P f hf h).1

def thm_12_3_subseqIncrement {Ω : Type}
    (R : ℕ → Ω → ℝ) (n : ℕ → ℕ) : ℕ → Ω → ℝ :=
  fun k ω => R (n (k + 1)) ω - R (n k) ω

theorem thm_12_3_subseqIncrement_measurable
    {Ω : Type} [MeasurableSpace Ω]
    {R : ℕ → Ω → ℝ} {n : ℕ → ℕ}
    (hR : ∀ m, Measurable (R m)) :
    ∀ k, Measurable ((thm_12_3_subseqIncrement R n) k) := by
  intro k
  unfold thm_12_3_subseqIncrement
  exact (hR (n (k + 1))).sub (hR (n k))

theorem thm_12_3_prob_7_7_subseq_increments
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {R : ℕ → Ω → ℝ} {n : ℕ → ℕ}
    (hR : ∀ m, Measurable (R m))
    (hAbs : HasFiniteAbsIntegralSeries P (thm_12_3_subseqIncrement R n)) :
    ∀ᵐ ω ∂P, ∃ L : ℝ,
      Tendsto
        (fun N => ∑ k ∈ Finset.range N,
          thm_12_3_subseqIncrement R n k ω)
        atTop (𝓝 L) :=
  thm_12_3_series_ae_limit_input
    (P := P)
    (f := thm_12_3_subseqIncrement R n)
    (thm_12_3_subseqIncrement_measurable hR)
    hAbs

theorem thm_12_3_hasFiniteAbsIntegralSeries_of_eLpNorm_two_tsum_ne_top
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (hf : ∀ k, Measurable (f k))
    (h2 : (∑' k, eLpNorm (f k) (2 : ℝ≥0∞) P) ≠ ∞) :
    HasFiniteAbsIntegralSeries P f := by
  refine ⟨∑' k, ∫⁻ ω, ‖f k ω‖₊ ∂P, ?_, ENNReal.summable.hasSum⟩
  have hle : (∑' k, ∫⁻ ω, ‖f k ω‖₊ ∂P) ≤
      ∑' k, eLpNorm (f k) (2 : ℝ≥0∞) P := by
    refine ENNReal.tsum_le_tsum ?_
    intro k
    simpa [eLpNorm_one_eq_lintegral_enorm, enorm_eq_nnnorm] using
      (eLpNorm_le_eLpNorm_of_exponent_le (μ := P) (f := f k)
        (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)
        (hf k).aestronglyMeasurable)
  exact ne_top_of_le_ne_top h2 hle

theorem thm_12_3_hasFiniteAbsIntegralSeries_of_eLpNorm_two_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (hf : ∀ k, Measurable (f k))
    (B : ℕ → ℝ) (hBsum : Summable B)
    (hBound : ∀ k, eLpNorm (f k) (2 : ℝ≥0∞) P ≤ ENNReal.ofReal (B k)) :
    HasFiniteAbsIntegralSeries P f := by
  refine ⟨∑' k, ∫⁻ ω, ‖f k ω‖₊ ∂P, ?_, ENNReal.summable.hasSum⟩
  have hle_one_two : ∀ k, (∫⁻ ω, ‖f k ω‖₊ ∂P) ≤
      eLpNorm (f k) (2 : ℝ≥0∞) P := by
    intro k
    simpa [eLpNorm_one_eq_lintegral_enorm, enorm_eq_nnnorm] using
      (eLpNorm_le_eLpNorm_of_exponent_le (μ := P) (f := f k)
        (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (by norm_num)
        (hf k).aestronglyMeasurable)
  have hle : (∑' k, ∫⁻ ω, ‖f k ω‖₊ ∂P) ≤
      ∑' k, ENNReal.ofReal (B k) := by
    refine ENNReal.tsum_le_tsum ?_
    intro k
    exact (hle_one_two k).trans (hBound k)
  exact ne_top_of_le_ne_top hBsum.tsum_ofReal_ne_top hle

theorem thm_12_3_prob_7_7_subseq_increments_of_l2_tsum
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {R : ℕ → Ω → ℝ} {n : ℕ → ℕ}
    (hR : ∀ m, Measurable (R m))
    (h2 : (∑' k,
      eLpNorm (thm_12_3_subseqIncrement R n k) (2 : ℝ≥0∞) P) ≠ ∞) :
    ∀ᵐ ω ∂P, ∃ L : ℝ,
      Tendsto
        (fun N => ∑ k ∈ Finset.range N,
          thm_12_3_subseqIncrement R n k ω)
        atTop (𝓝 L) :=
  thm_12_3_prob_7_7_subseq_increments P hR
    (thm_12_3_hasFiniteAbsIntegralSeries_of_eLpNorm_two_tsum_ne_top
      P (thm_12_3_subseqIncrement R n)
      (thm_12_3_subseqIncrement_measurable hR) h2)

theorem thm_12_3_prob_7_7_subseq_increments_of_l2_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {R : ℕ → Ω → ℝ} {n : ℕ → ℕ}
    (hR : ∀ m, Measurable (R m))
    (B : ℕ → ℝ) (hBsum : Summable B)
    (hBound : ∀ k,
      eLpNorm (thm_12_3_subseqIncrement R n k) (2 : ℝ≥0∞) P ≤
        ENNReal.ofReal (B k)) :
    ∀ᵐ ω ∂P, ∃ L : ℝ,
      Tendsto
        (fun N => ∑ k ∈ Finset.range N,
          thm_12_3_subseqIncrement R n k ω)
        atTop (𝓝 L) :=
  thm_12_3_prob_7_7_subseq_increments P hR
    (thm_12_3_hasFiniteAbsIntegralSeries_of_eLpNorm_two_bound
      P (thm_12_3_subseqIncrement R n)
      (thm_12_3_subseqIncrement_measurable hR) B hBsum hBound)

theorem thm_12_3_l2_coe_measurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω →₂[P] ℝ) :
    ∀ m, Measurable (fun ω => (F m : Ω → ℝ) ω) := by
  intro m
  exact (MeasureTheory.Lp.stronglyMeasurable (F m)).measurable

theorem thm_12_3_subseqIncrement_eLpNorm_eq_dist
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω →₂[P] ℝ) (n : ℕ → ℕ) (k : ℕ) :
    eLpNorm (thm_12_3_subseqIncrement (fun m => (F m : Ω → ℝ)) n k)
        (2 : ℝ≥0∞) P =
      ENNReal.ofReal (dist (F (n (k + 1))) (F (n k))) := by
  unfold thm_12_3_subseqIncrement
  rw [← MeasureTheory.Lp.edist_dist]
  rw [MeasureTheory.Lp.edist_def]
  refine eLpNorm_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_sub (F (n (k + 1))) (F (n k))] with ω hω
  simp [hω]

theorem thm_12_3_pair_eLpNorm_eq_dist
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω →₂[P] ℝ) (a b : ℕ) :
    eLpNorm ((fun ω => (F a : Ω → ℝ) ω) - (fun ω => (F b : Ω → ℝ) ω))
        (2 : ℝ≥0∞) P =
      ENNReal.ofReal (dist (F a) (F b)) := by
  rw [← MeasureTheory.Lp.edist_dist]
  rw [MeasureTheory.Lp.edist_def]

theorem thm_12_3_prob_7_7_l2_coe_subseq_increments
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω →₂[P] ℝ) (n : ℕ → ℕ)
    (hsum : Summable fun k => dist (F (n (k + 1))) (F (n k))) :
    ∀ᵐ ω ∂P, ∃ L : ℝ,
      Tendsto
        (fun N => ∑ k ∈ Finset.range N,
          thm_12_3_subseqIncrement (fun m => (F m : Ω → ℝ)) n k ω)
        atTop (𝓝 L) :=
  thm_12_3_prob_7_7_subseq_increments_of_l2_bound
    P (thm_12_3_l2_coe_measurable P F)
    (fun k => dist (F (n (k + 1))) (F (n k))) hsum
    (by
      intro k
      rw [thm_12_3_subseqIncrement_eLpNorm_eq_dist P F n k])

theorem thm_12_3_prob_7_7_l2_cauchy_selected_subseq_increments
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω →₂[P] ℝ) (hF : CauchySeq F) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ᵐ ω ∂P, ∃ L : ℝ,
        Tendsto
          (fun N => ∑ k ∈ Finset.range N,
            thm_12_3_subseqIncrement (fun m => (F m : Ω → ℝ)) n k ω)
          atTop (𝓝 L) := by
  rcases Metric.exists_subseq_summable_dist_of_cauchySeq F hF with
    ⟨n, hn, hsum⟩
  exact ⟨n, hn, thm_12_3_prob_7_7_l2_coe_subseq_increments P F n hsum⟩

theorem thm_12_3_subseq_telescoping
    {Ω : Type} (R : ℕ → Ω → ℝ) (n : ℕ → ℕ) (ω : Ω) :
    ∀ N, R (n N) ω =
      R (n 0) ω +
        ∑ k ∈ Finset.range N, thm_12_3_subseqIncrement R n k ω := by
  intro N
  induction N with
  | zero =>
      simp [thm_12_3_subseqIncrement]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      change R (n (N + 1)) ω = R (n 0) ω +
        ((∑ x ∈ Finset.range N, thm_12_3_subseqIncrement R n x ω) +
          (R (n (N + 1)) ω - R (n N) ω))
      calc
        R (n (N + 1)) ω =
            R (n N) ω + (R (n (N + 1)) ω - R (n N) ω) := by
          ring
        _ = (R (n 0) ω +
              ∑ x ∈ Finset.range N, thm_12_3_subseqIncrement R n x ω) +
              (R (n (N + 1)) ω - R (n N) ω) := by
          rw [ih]
        _ = R (n 0) ω +
              ((∑ x ∈ Finset.range N, thm_12_3_subseqIncrement R n x ω) +
                (R (n (N + 1)) ω - R (n N) ω)) := by
          ring

theorem thm_12_3_subseq_tendsto_of_increment_tendsto
    {Ω : Type} (R : ℕ → Ω → ℝ) (n : ℕ → ℕ) (ω : Ω) {L : ℝ}
    (hL :
      Tendsto
        (fun N => ∑ k ∈ Finset.range N, thm_12_3_subseqIncrement R n k ω)
        atTop (𝓝 L)) :
    Tendsto (fun N => R (n N) ω) atTop (𝓝 (R (n 0) ω + L)) := by
  have hsum :=
    Filter.Tendsto.const_add (R (n 0) ω) hL
  refine hsum.congr' ?_
  exact Filter.Eventually.of_forall fun N =>
    (thm_12_3_subseq_telescoping R n ω N).symm

theorem thm_12_3_subseq_ae_tendsto_of_increment_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {R : ℕ → Ω → ℝ} {n : ℕ → ℕ}
    (hinc :
      ∀ᵐ ω ∂P, ∃ L : ℝ,
        Tendsto
          (fun N => ∑ k ∈ Finset.range N,
            thm_12_3_subseqIncrement R n k ω)
          atTop (𝓝 L)) :
    ∀ᵐ ω ∂P, ∃ L : ℝ,
      Tendsto (fun N => R (n N) ω) atTop (𝓝 L) := by
  filter_upwards [hinc] with ω hω
  rcases hω with ⟨L, hL⟩
  exact ⟨R (n 0) ω + L,
    thm_12_3_subseq_tendsto_of_increment_tendsto R n ω hL⟩

theorem thm_12_3_l2_cauchy_selected_subseq_ae_tendsto
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω →₂[P] ℝ) (hF : CauchySeq F) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ᵐ ω ∂P, ∃ L : ℝ,
        Tendsto (fun N => (F (n N) : Ω → ℝ) ω) atTop (𝓝 L) := by
  rcases thm_12_3_prob_7_7_l2_cauchy_selected_subseq_increments P F hF with
    ⟨n, hn, hinc⟩
  exact ⟨n, hn,
    thm_12_3_subseq_ae_tendsto_of_increment_ae
      P (R := fun m => (F m : Ω → ℝ)) (n := n) hinc⟩

theorem thm_12_3_l2_cauchy_selected_subseq_measurable_candidate
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω →₂[P] ℝ) (hF : CauchySeq F) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∃ f_lim : Ω → ℝ,
      StronglyMeasurable f_lim ∧
        ∀ᵐ ω ∂P,
          Tendsto (fun N => (F (n N) : Ω → ℝ) ω)
            atTop (𝓝 (f_lim ω)) := by
  rcases thm_12_3_l2_cauchy_selected_subseq_ae_tendsto P F hF with
    ⟨n, hn, hsubseq⟩
  have hmeas :
      ∀ N, AEStronglyMeasurable (fun ω => (F (n N) : Ω → ℝ) ω) P := by
    intro N
    exact (MeasureTheory.Lp.stronglyMeasurable (F (n N))).aestronglyMeasurable
  rcases exists_stronglyMeasurable_limit_of_tendsto_ae hmeas hsubseq with
    ⟨f_lim, hf_lim, hlim⟩
  exact ⟨n, hn, f_lim, hf_lim, hlim⟩

theorem thm_12_3_inner_interface {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) :
    def_12_2 P X Y = l2Inner P X Y :=
  rfl

theorem thm_12_3_l2_triangle {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω →₂[P] ℝ) :
    ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ :=
  thm_12_2 (𝕜 := ℝ) (E := Ω →₂[P] ℝ) X Y

theorem thm_12_3_l2_liminf_bound_of_ae_tendsto
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) P)
    {f_lim : Ω → ℝ}
    (h_lim : ∀ᵐ x ∂P, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm f_lim 2 P ≤ atTop.liminf fun n => eLpNorm (f n) 2 P := by
  exact MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := P)
    (p := (2 : ℝ≥0∞)) hf f_lim h_lim

theorem thm_12_3_fatou_sqdiff_liminf_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g f_lim : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (hg : AEStronglyMeasurable g P)
    (hlim : ∀ᵐ x ∂P, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x))) :
    eLpNorm (f_lim - g) 2 P ≤
      atTop.liminf fun n => eLpNorm (f n - g) 2 P := by
  have hdiff_meas : ∀ n, AEStronglyMeasurable (f n - g) P := by
    intro n
    exact (hf n).sub hg
  have hdiff_lim : ∀ᵐ x ∂P,
      Tendsto (fun n => (f n - g) x) atTop (𝓝 ((f_lim - g) x)) := by
    filter_upwards [hlim] with x hx
    simpa [Pi.sub_apply] using hx.sub tendsto_const_nhds
  exact MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := P)
    (p := (2 : ℝ≥0∞)) hdiff_meas (f_lim - g) hdiff_lim

theorem thm_12_3_fatou_sqdiff_bound_of_eventual_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g f_lim : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (hg : AEStronglyMeasurable g P)
    (hlim : ∀ᵐ x ∂P, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)))
    {A : ℝ≥0∞}
    (hbound : ∀ᶠ n in atTop, eLpNorm (f n - g) 2 P ≤ A) :
    eLpNorm (f_lim - g) 2 P ≤ A := by
  have hfatou := thm_12_3_fatou_sqdiff_liminf_bound P f g f_lim hf hg hlim
  have hliminf_le : (atTop.liminf fun n => eLpNorm (f n - g) 2 P) ≤ A := by
    exact Filter.liminf_le_of_frequently_le hbound.frequently
  exact hfatou.trans hliminf_le

theorem thm_12_3_fatou_sqdiff_tail_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (f_lim : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (hlim : ∀ᵐ x ∂P, Tendsto (fun n => f n x) atTop (𝓝 (f_lim x)))
    {A : ℝ≥0∞}
    (hTail : ∀ᶠ k in atTop, ∀ᶠ j in atTop,
      eLpNorm (f j - f k) 2 P ≤ A) :
    ∀ᶠ k in atTop, eLpNorm (f_lim - f k) 2 P ≤ A := by
  filter_upwards [hTail] with k hk
  exact thm_12_3_fatou_sqdiff_bound_of_eventual_bound
    P f (f k) f_lim hf (hf k) hlim hk

theorem thm_12_3_l2_cauchy_selected_subseq_fatou_tail_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω →₂[P] ℝ) (hF : CauchySeq F) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∃ f_lim : Ω → ℝ,
      StronglyMeasurable f_lim ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun N => (F (n N) : Ω → ℝ) ω) atTop (𝓝 (f_lim ω))) ∧
      ∀ᶠ k in atTop,
        eLpNorm (f_lim - fun ω => (F (n k) : Ω → ℝ) ω) 2 P
          ≤ ENNReal.ofReal ε := by
  rcases thm_12_3_l2_cauchy_selected_subseq_measurable_candidate P F hF with
    ⟨n, hn, f_lim, hf_lim, hlim⟩
  have hf : ∀ N, AEStronglyMeasurable (fun ω => (F (n N) : Ω → ℝ) ω) P := by
    intro N
    exact (MeasureTheory.Lp.stronglyMeasurable (F (n N))).aestronglyMeasurable
  have htail_dist : ∀ᶠ k in atTop, ∀ᶠ j in atTop,
      dist (F (n j)) (F (n k)) < ε := by
    rcases (Metric.cauchySeq_iff.1 hF ε hε) with ⟨N, hN⟩
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro k hk
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro j hj
    exact hN (n j) (le_trans hj ((StrictMono.id_le hn) j))
      (n k) (le_trans hk ((StrictMono.id_le hn) k))
  have hTail : ∀ᶠ k in atTop, ∀ᶠ j in atTop,
      eLpNorm ((fun ω => (F (n j) : Ω → ℝ) ω) -
          (fun ω => (F (n k) : Ω → ℝ) ω)) 2 P ≤ ENNReal.ofReal ε := by
    filter_upwards [htail_dist] with k hk
    filter_upwards [hk] with j hj
    rw [thm_12_3_pair_eLpNorm_eq_dist P F (n j) (n k)]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hj)
  exact ⟨n, hn, f_lim, hf_lim, hlim,
    thm_12_3_fatou_sqdiff_tail_bound P
      (fun N => fun ω => (F (n N) : Ω → ℝ) ω) f_lim hf hlim hTail⟩

theorem thm_12_3_l2_cauchy_selected_subseq_eLpNorm_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω →₂[P] ℝ) (hF : CauchySeq F) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∃ f_lim : Ω → ℝ,
      StronglyMeasurable f_lim ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun N => (F (n N) : Ω → ℝ) ω) atTop (𝓝 (f_lim ω))) ∧
      Tendsto
        (fun k : ℕ => eLpNorm (f_lim - fun ω => (F (n k) : Ω → ℝ) ω) 2 P)
        atTop (𝓝 0) := by
  rcases thm_12_3_l2_cauchy_selected_subseq_measurable_candidate P F hF with
    ⟨n, hn, f_lim, hf_lim, hlim⟩
  have hf : ∀ N, AEStronglyMeasurable (fun ω => (F (n N) : Ω → ℝ) ω) P := by
    intro N
    exact (MeasureTheory.Lp.stronglyMeasurable (F (n N))).aestronglyMeasurable
  have htend :
      Tendsto
        (fun k : ℕ => eLpNorm (f_lim - fun ω => (F (n k) : Ω → ℝ) ω) 2 P)
        atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases hεtop : ε = ⊤
    · subst ε
      filter_upwards with k
      exact le_top
    · have hε0 : ε ≠ 0 := ne_of_gt hε
      have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε0 hεtop
      have htail_dist : ∀ᶠ k in atTop, ∀ᶠ j in atTop,
          dist (F (n j)) (F (n k)) < ε.toReal := by
        rcases (Metric.cauchySeq_iff.1 hF ε.toReal hεreal) with ⟨N, hN⟩
        refine eventually_atTop.2 ⟨N, ?_⟩
        intro k hk
        refine eventually_atTop.2 ⟨N, ?_⟩
        intro j hj
        exact hN (n j) (le_trans hj ((StrictMono.id_le hn) j))
          (n k) (le_trans hk ((StrictMono.id_le hn) k))
      have hTail : ∀ᶠ k in atTop, ∀ᶠ j in atTop,
          eLpNorm ((fun ω => (F (n j) : Ω → ℝ) ω) -
              (fun ω => (F (n k) : Ω → ℝ) ω)) 2 P ≤ ε := by
        filter_upwards [htail_dist] with k hk
        filter_upwards [hk] with j hj
        rw [thm_12_3_pair_eLpNorm_eq_dist P F (n j) (n k)]
        rw [← ENNReal.ofReal_toReal hεtop]
        exact ENNReal.ofReal_le_ofReal (le_of_lt hj)
      exact thm_12_3_fatou_sqdiff_tail_bound P
        (fun N => fun ω => (F (n N) : Ω → ℝ) ω) f_lim hf hlim hTail
  exact ⟨n, hn, f_lim, hf_lim, hlim, htend⟩

theorem thm_12_3_l2_cauchy_selected_subseq_memLp_limit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω →₂[P] ℝ) (hF : CauchySeq F) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∃ f_lim : Ω → ℝ,
      MemLp f_lim 2 P ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun N => (F (n N) : Ω → ℝ) ω) atTop (𝓝 (f_lim ω))) ∧
      Tendsto
        (fun k : ℕ => eLpNorm (f_lim - fun ω => (F (n k) : Ω → ℝ) ω) 2 P)
        atTop (𝓝 0) := by
  rcases thm_12_3_l2_cauchy_selected_subseq_eLpNorm_tendsto_zero P F hF with
    ⟨n, hn, f_lim, hf_lim, hlim, htend⟩
  have hf : ∀ k, MemLp (fun ω => (F (n k) : Ω → ℝ) ω) 2 P := by
    intro k
    exact MeasureTheory.Lp.memLp (F (n k))
  have htend' :
      Tendsto
        (fun k : ℕ => eLpNorm ((fun ω => (F (n k) : Ω → ℝ) ω) - f_lim) 2 P)
        atTop (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ htend
    filter_upwards with k
    have hneg : ((fun ω => (F (n k) : Ω → ℝ) ω) - f_lim) =
        -(f_lim - fun ω => (F (n k) : Ω → ℝ) ω) := by
      funext ω
      simp
    rw [hneg, eLpNorm_neg]
  have hf_lim_mem : MemLp f_lim 2 P :=
    MeasureTheory.Lp.memLp_of_cauchy_tendsto (μ := P) (p := (2 : ℝ≥0∞))
      (hp := by norm_num) hf f_lim hf_lim.aestronglyMeasurable htend'
  exact ⟨n, hn, f_lim, hf_lim_mem, hlim, htend⟩

theorem thm_12_3_l2_cauchy_selected_subseq_tendsto_toLp
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω →₂[P] ℝ) (hF : CauchySeq F) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∃ f_lim : Ω → ℝ, ∃ hf_lim : MemLp f_lim 2 P,
      Tendsto (fun k : ℕ => F (n k)) atTop
        (𝓝 (MeasureTheory.MemLp.toLp f_lim hf_lim)) := by
  rcases thm_12_3_l2_cauchy_selected_subseq_memLp_limit P F hF with
    ⟨n, hn, f_lim, hf_lim, _hlim, htend⟩
  have hquot :
      Tendsto (fun k : ℕ => F (n k)) atTop
        (𝓝 (MeasureTheory.MemLp.toLp f_lim hf_lim)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : 0 < ENNReal.ofReal (ε / 2) := by
      exact ENNReal.ofReal_pos.mpr (by linarith)
    have hsmall :=
      (ENNReal.tendsto_nhds_zero.mp htend) (ENNReal.ofReal (ε / 2)) hε2
    rcases eventually_atTop.1 hsmall with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    have hle := hN k hk
    have hfN : MemLp (fun ω => (F (n k) : Ω → ℝ) ω) 2 P :=
      MeasureTheory.Lp.memLp (F (n k))
    have hle' :
        ENNReal.ofReal
          (dist (F (n k)) (MeasureTheory.MemLp.toLp f_lim hf_lim)) ≤
            ENNReal.ofReal (ε / 2) := by
      rw [← MeasureTheory.Lp.edist_dist]
      rw [← MeasureTheory.Lp.toLp_coeFn (F (n k)) hfN]
      rw [MeasureTheory.Lp.edist_toLp_toLp]
      have hneg : ((fun ω => (F (n k) : Ω → ℝ) ω) - f_lim) =
          -(f_lim - fun ω => (F (n k) : Ω → ℝ) ω) := by
        funext ω
        simp
      rw [hneg, eLpNorm_neg]
      exact hle
    have hdist_le :
        dist (F (n k)) (MeasureTheory.MemLp.toLp f_lim hf_lim) ≤ ε / 2 := by
      exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 hle'
    exact lt_of_le_of_lt hdist_le (by linarith)
  exact ⟨n, hn, f_lim, hf_lim, hquot⟩

theorem thm_12_3_cauchySeq_has_source_limit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω →₂[P] ℝ) (hF : CauchySeq F) :
    ∃ f₂ : Ω →₂[P] ℝ, Tendsto F atTop (𝓝 f₂) := by
  rcases thm_12_3_l2_cauchy_selected_subseq_tendsto_toLp P F hF with
    ⟨n, hn, f_lim, hf_lim, hsub⟩
  let f₂ : Ω →₂[P] ℝ := MeasureTheory.MemLp.toLp f_lim hf_lim
  have hcomp : Tendsto (F ∘ n) atTop (𝓝 f₂) := by
    simpa [Function.comp_def, f₂] using hsub
  exact ⟨f₂, tendsto_nhds_of_cauchySeq_of_subseq hF hn.tendsto_atTop hcomp⟩

theorem thm_12_3_completeSpace_of_source_cauchySeq_limit
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    CompleteSpace (Ω →₂[P] ℝ) := by
  exact Metric.complete_of_cauchySeq_tendsto
    (fun F hF => thm_12_3_cauchySeq_has_source_limit P F hF)

theorem thm_12_3_controlled_cauchy_ae_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, AEStronglyMeasurable (f n) P)
    {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (f n - f m) 2 P < B N) :
    ∀ᵐ x ∂P, ∃ l : ℝ, atTop.Tendsto (fun n => f n x) (𝓝 l) := by
  exact MeasureTheory.Lp.ae_tendsto_of_cauchy_eLpNorm (μ := P)
    (p := (2 : ℝ≥0∞)) hf (by norm_num) hB h_cau

theorem thm_12_3_controlled_cauchy_source_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 P)
    {B : ℕ → ℝ≥0∞} (hB : ∑' i, B i ≠ ∞)
    (h_cau : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (f n - f m) 2 P < B N) :
    ∃ f_lim : Ω → ℝ, MemLp f_lim 2 P ∧
      atTop.Tendsto (fun n => eLpNorm (f n - f_lim) 2 P) (𝓝 0) := by
  exact MeasureTheory.Lp.cauchy_complete_eLpNorm (μ := P) (E := ℝ)
    (p := (2 : ℝ≥0∞)) (by norm_num) hf hB h_cau

theorem thm_12_3_completeSpace_of_controlled_source_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) :
    CompleteSpace (Ω →₂[P] ℝ) := by
  exact MeasureTheory.Lp.completeSpace_lp_of_cauchy_complete_eLpNorm
    (μ := P) (E := ℝ) (p := (2 : ℝ≥0∞))
    (H := by
      intro f hf B hB h_cau
      exact thm_12_3_controlled_cauchy_source_limit
        (P := P) f hf hB.ne h_cau)

theorem thm_12_3_probability_source
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    CompleteSpace (Ω →₂[P] ℝ) := by
  exact thm_12_3_completeSpace_of_source_cauchySeq_limit P

theorem thm_12_3_textbookHilbert_probability_source
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    def_12_3 ℝ (Ω →₂[P] ℝ) := by
  dsimp [def_12_3, TextbookHilbertSpace]
  exact (textbookCompleteSpace_iff_complete (Ω →₂[P] ℝ)).2
    (thm_12_3_probability_source P)

theorem thm_12_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    CompleteSpace (Ω →₂[P] ℝ) := by
  exact thm_12_3_completeSpace_of_controlled_source_limit P

theorem thm_12_3_textbookHilbert {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    def_12_3 ℝ (Ω →₂[P] ℝ) := by
  dsimp [def_12_3, TextbookHilbertSpace]
  exact (textbookCompleteSpace_iff_complete (Ω →₂[P] ℝ)).2 (thm_12_3 P)

theorem thm_12_3_complex {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] :
    CompleteSpace (Ω →₂[P] ℂ) := by
  infer_instance
