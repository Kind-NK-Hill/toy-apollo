/-
TASK ID: prob_7_3
TYPE: Problem
SOURCE PLAN: 30_chap7_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.prob_7_3_lebesgue_support
import ToyApollo.Output.thm_1_1_common_limit
import ToyApollo.Output.thm_7_8_ioc_bridge_support
import ToyApollo.Output.thm_7_9_endpoint_support

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set Filter

noncomputable section

theorem prob_7_3_relativeDiscontinuitySet_null_of_largeOscillationSet_nulls
    (μ : Measure ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hNull : ∀ n : ℕ,
      (μ.restrict (Icc a b)) (prob_7_3_largeOscillationSet f a b n) = 0) :
    (μ.restrict (Icc a b)) (prob_7_3_relativeDiscontinuitySetOn f a b) = 0 := by
  have hUnion :
      (μ.restrict (Icc a b))
          (⋃ n : ℕ, prob_7_3_largeOscillationSet f a b n) = 0 := by
    exact measure_iUnion_null hNull
  refine measure_mono_null ?_ hUnion
  intro x hx
  rcases hx with ⟨hxI, hxdisc⟩
  rcases prob_7_3_discontinuity_within_implies_largeOscillationSet_mem
      (f := f) (a := a) (b := b) hxI hxdisc with
    ⟨n, hn⟩
  exact mem_iUnion.mpr ⟨n, hn⟩

theorem prob_7_3_largeOscillationSet_nulls_imply_ae_continuity
    (μ : Measure ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hNull : ∀ n : ℕ,
      (μ.restrict (Icc a b)) (prob_7_3_largeOscillationSet f a b n) = 0) :
    ∀ᵐ x ∂(μ.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x := by
  have hDiscNull :
      (μ.restrict (Icc a b)) (prob_7_3_relativeDiscontinuitySetOn f a b) = 0 :=
    prob_7_3_relativeDiscontinuitySet_null_of_largeOscillationSet_nulls
      (μ := μ) (a := a) (b := b) (f := f) hNull
  have hNotDisc :
      ∀ᵐ x ∂(μ.restrict (Icc a b)),
        x ∉ prob_7_3_relativeDiscontinuitySetOn f a b :=
    compl_mem_ae_iff.2 hDiscNull
  filter_upwards [ae_restrict_mem measurableSet_Icc, hNotDisc] with x hxI hxNotDisc
  by_contra hxCont
  exact hxNotDisc ⟨hxI, hxCont⟩

theorem prob_7_3_largeOscillationSet_subset_relativeDiscontinuitySetOn
    {a b : ℝ} {f : ℝ → ℝ} (n : ℕ) :
    prob_7_3_largeOscillationSet f a b n ⊆
      prob_7_3_relativeDiscontinuitySetOn f a b := by
  intro x hx
  rcases hx with ⟨hxI, heta, hlocal⟩
  refine ⟨hxI, ?_⟩
  intro hcont
  rcases prob_7_3_continuousWithinAt_local_two_point_oscillation
      (f := f) (a := a) (b := b) (x := x)
      hcont heta with
    ⟨delta, hdelta, hsmall⟩
  rcases hlocal delta hdelta with
    ⟨y, hyI, hydist, z, hzI, hzdist, hyz⟩
  exact not_le_of_gt (hsmall y hyI hydist z hzI hzdist) hyz

theorem prob_7_3_ae_continuity_implies_largeOscillationSet_nulls
    (μ : Measure ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ∀ᵐ x ∂(μ.restrict (Icc a b)),
      ContinuousWithinAt f (Icc a b) x) :
    ∀ n : ℕ, (μ.restrict (Icc a b)) (prob_7_3_largeOscillationSet f a b n) = 0 := by
  intro n
  have hDisc :
      (μ.restrict (Icc a b)) (prob_7_3_relativeDiscontinuitySetOn f a b) = 0 :=
    prob_7_3_relativeDiscontinuitySetOn_null_of_ae_continuity
      (μ := μ) (a := a) (b := b) (f := f) hcont
  exact measure_mono_null
    (prob_7_3_largeOscillationSet_subset_relativeDiscontinuitySetOn
      (a := a) (b := b) (f := f) n)
    hDisc

theorem prob_7_3_ae_continuity_iff_largeOscillationSet_nulls
    (μ : Measure ℝ) {a b : ℝ} {f : ℝ → ℝ} :
    (∀ᵐ x ∂(μ.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x) ↔
      ∀ n : ℕ,
        (μ.restrict (Icc a b)) (prob_7_3_largeOscillationSet f a b n) = 0 := by
  constructor
  · exact prob_7_3_ae_continuity_implies_largeOscillationSet_nulls
      (μ := μ) (a := a) (b := b) (f := f)
  · exact prob_7_3_largeOscillationSet_nulls_imply_ae_continuity
      (μ := μ) (a := a) (b := b) (f := f)

theorem prob_7_3_isClosed_largeOscillationSet
    {a b : ℝ} {f : ℝ → ℝ} (n : ℕ) :
    IsClosed (prob_7_3_largeOscillationSet f a b n) := by
  rw [← closure_subset_iff_isClosed]
  intro x hxcl
  have hsubsetI :
      prob_7_3_largeOscillationSet f a b n ⊆ Icc a b := by
    intro y hy
    exact hy.1
  have hxI : x ∈ Icc a b := by
    have hxclI : x ∈ closure (Icc a b) := closure_mono hsubsetI hxcl
    simpa [isClosed_Icc.closure_eq] using hxclI
  refine ⟨hxI, by positivity, ?_⟩
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by linarith
  rcases (Metric.mem_closure_iff.mp hxcl (δ / 2) hδ2) with
    ⟨w, hw, hxw⟩
  rcases hw with ⟨_hwI, _heta, hwlocal⟩
  rcases hwlocal (δ / 2) hδ2 with
    ⟨y, hyI, hyw, z, hzI, hzw, hyz⟩
  refine ⟨y, hyI, ?_, z, hzI, ?_, hyz⟩
  · have hyw_dist : dist y w < δ / 2 := by
      simpa [Real.dist_eq] using hyw
    have hwx_dist : dist w x < δ / 2 := by
      simpa [dist_comm] using hxw
    have hyx_le : dist y x ≤ dist y w + dist w x := dist_triangle y w x
    have hyx_lt : dist y x < δ := by
      linarith
    simpa [Real.dist_eq] using hyx_lt
  · have hzw_dist : dist z w < δ / 2 := by
      simpa [Real.dist_eq] using hzw
    have hwx_dist : dist w x < δ / 2 := by
      simpa [dist_comm] using hxw
    have hzx_le : dist z x ≤ dist z w + dist w x := dist_triangle z w x
    have hzx_lt : dist z x < δ := by
      linarith
    simpa [Real.dist_eq] using hzx_lt

theorem prob_7_3_measurableSet_largeOscillationSet
    {a b : ℝ} {f : ℝ → ℝ} (n : ℕ) :
    MeasurableSet (prob_7_3_largeOscillationSet f a b n) :=
  (prob_7_3_isClosed_largeOscillationSet (a := a) (b := b) (f := f) n).measurableSet

theorem prob_7_3_relativeDiscontinuitySetOn_measurable
    {a b : ℝ} {f : ℝ → ℝ} :
    MeasurableSet (prob_7_3_relativeDiscontinuitySetOn f a b) := by
  have hEq :
      prob_7_3_relativeDiscontinuitySetOn f a b =
        ⋃ n : ℕ, prob_7_3_largeOscillationSet f a b n := by
    ext x
    constructor
    · intro hx
      rcases prob_7_3_discontinuity_within_implies_largeOscillationSet_mem
          (f := f) (a := a) (b := b) (x := x) hx.1 hx.2 with
        ⟨n, hn⟩
      exact mem_iUnion.mpr ⟨n, hn⟩
    · intro hx
      rcases mem_iUnion.mp hx with ⟨n, hn⟩
      exact prob_7_3_largeOscillationSet_subset_relativeDiscontinuitySetOn
        (a := a) (b := b) (f := f) n hn
  rw [hEq]
  exact MeasurableSet.iUnion fun n =>
    prob_7_3_measurableSet_largeOscillationSet (a := a) (b := b) (f := f) n

theorem prob_7_3_ae_continuity_implies_aestronglyMeasurable_restrict_Icc
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hcont : ∀ᵐ x ∂(F.measure.restrict (Icc a b)),
      ContinuousWithinAt f (Icc a b) x) :
    AEStronglyMeasurable f (F.measure.restrict (Icc a b)) := by
  classical
  let D : Set ℝ := prob_7_3_relativeDiscontinuitySetOn f a b
  let C : Set ℝ := Icc a b \ D
  have hDmeas : MeasurableSet D := by
    dsimp [D]
    exact prob_7_3_relativeDiscontinuitySetOn_measurable (a := a) (b := b) (f := f)
  have hDnull : (F.measure.restrict (Icc a b)) D = 0 := by
    dsimp [D]
    exact prob_7_3_relativeDiscontinuitySetOn_null_of_ae_continuity
      (μ := F.measure) (a := a) (b := b) (f := f) hcont
  have hCmeas : MeasurableSet C := by
    dsimp [C]
    exact measurableSet_Icc.diff hDmeas
  have hContC : ContinuousOn f C := by
    intro x hx
    have hxI : x ∈ Icc a b := hx.1
    have hxNotD : x ∉ D := hx.2
    have hxContI : ContinuousWithinAt f (Icc a b) x := by
      by_contra hbad
      exact hxNotD ⟨hxI, hbad⟩
    exact hxContI.mono (by
      intro y hy
      exact hy.1)
  let g : ℝ → ℝ :=
    Function.extend (fun x : C => (x : ℝ)) (fun x : C => f (x : ℝ)) (fun _ : ℝ => 0)
  have hgStrong : StronglyMeasurable g := by
    dsimp [g]
    exact (MeasurableEmbedding.subtype_coe hCmeas).stronglyMeasurable_extend
      ((continuousOn_iff_continuous_restrict.mp hContC).stronglyMeasurable)
      stronglyMeasurable_const
  have hCae : ∀ᵐ x ∂(F.measure.restrict (Icc a b)), x ∈ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, compl_mem_ae_iff.mpr hDnull] with x hxI hxNotD
    exact ⟨hxI, hxNotD⟩
  have hgf : g =ᵐ[F.measure.restrict (Icc a b)] f := by
    filter_upwards [hCae] with x hxC
    dsimp [g]
    simpa using
      (Subtype.coe_injective.extend_apply
        (fun y : C => f (y : ℝ)) (fun _ : ℝ => 0) ⟨x, hxC⟩)
  exact hgStrong.aestronglyMeasurable.congr hgf

theorem prob_7_3_integrableOn_Icc_of_ae_continuous_bounded
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hBounded : ∃ M, ∀ x : ℝ, x ∈ Icc a b → |f x| ≤ M)
    (hcont : ∀ᵐ x ∂(F.measure.restrict (Icc a b)),
      ContinuousWithinAt f (Icc a b) x) :
    IntegrableOn f (Icc a b) F.measure := by
  rcases hBounded with ⟨M, hM⟩
  let C : ℝ := max 0 M
  have hAes : AEStronglyMeasurable f (F.measure.restrict (Icc a b)) :=
    prob_7_3_ae_continuity_implies_aestronglyMeasurable_restrict_Icc
      (F := F) (a := a) (b := b) (f := f) hcont
  have hCbound : ∀ᵐ x ∂(F.measure.restrict (Icc a b)), ‖f x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hxI
    have hx : |f x| ≤ C := (hM x hxI).trans (le_max_right 0 M)
    simpa [Real.norm_eq_abs] using hx
  exact IntegrableOn.of_bound
    (measure_Icc_lt_top (μ := F.measure) (a := a) (b := b))
    hAes C hCbound

theorem prob_7_3_ioc_integral_eq_rsIntegral_of_integrableOn
    (F : StieltjesFunction ℝ) {a b : ℝ} {f : ℝ → ℝ}
    (hIoc : IntegrableOn f (Ioc a b) F.measure)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hRS : RSIntegrable f F a b) :
    ∫ x in Ioc a b, f x ∂F.measure = rsIntegral f F a b hRS := by
  have hSqueeze : ∀ P : DarbouxRS.Partition a b,
      DarbouxRS.lowerSum P f F ≤ ∫ x in Ioc a b, f x ∂F.measure ∧
        ∫ x in Ioc a b, f x ∂F.measure ≤ DarbouxRS.upperSum P f F := by
    intro P
    exact thm_7_8_cellStep_integral_sandwich_Ioc F P f
      (thm_7_8_lowerCellStep_le_on_Ioc P f hBelow)
      (thm_7_8_le_upperCellStep_on_Ioc P f hAbove)
      hIoc
  exact thm_7_8_common_limit_squeeze_rsIntegral F hRS hSqueeze

theorem prob_7_3_bddAbove_bddBelow_of_abs_bound
    {a b : ℝ} {f : ℝ → ℝ}
    (hBounded : ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M) :
    BddAbove (f '' Icc a b) ∧ BddBelow (f '' Icc a b) := by
  rcases hBounded with ⟨M, hM⟩
  constructor
  · refine ⟨M, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact le_trans (le_abs_self (f x)) (hM x hx)
  · refine ⟨-M, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hxM : |f x| ≤ M := hM x hx
    have hxneg : -|f x| ≤ f x := neg_abs_le (f x)
    linarith

theorem prob_7_3_rsIntegrable_of_darbouxGapSmall
    {a b : ℝ} {f α : ℝ → ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hBounded : ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M)
    (hgap : Thm11SourceRoute.ClosedIntervalDarbouxGapSmall a b f α) :
    RSIntegrable f α a b := by
  rcases prob_7_3_bddAbove_bddBelow_of_abs_bound
      (a := a) (b := b) (f := f) hBounded with
    ⟨hAbove, hBelow⟩
  have hs : DarbouxRS.SourceHypotheses a b f α :=
    Thm11SourceRoute.sourceHypotheses_of_strict_task_hypotheses
      hab hα_mono hAbove hBelow
  rcases
      (Thm11SourceRoute.closedIntervalDarbouxCommonLimitFromGap_of_fineCauchy
        Thm11SourceRoute.closedIntervalDarbouxFineCauchyFromGap_proof)
        hs hgap with
    ⟨L, hUL⟩
  rw [← Thm11SourceRoute.common_limits_iff_rsIntegrable]
  exact ⟨L, hUL, Thm11SourceRoute.taggedCommonLimit_of_upperLowerCommonLimit hUL⟩

theorem prob_7_3_darbouxGapSmall_of_rsIntegrable
    {a b : ℝ} {f α : ℝ → ℝ}
    (hRS : RSIntegrable f α a b) :
    Thm11SourceRoute.ClosedIntervalDarbouxGapSmall a b f α := by
  intro eps heps
  exact (prob_7_3_rsIntegrable_unpacks_to_fine_upper_lower_gap_small hRS).2 eps heps

theorem prob_7_3_isFiniteMeasure_restrict_Icc
    (F : StieltjesFunction ℝ) {a b : ℝ} :
    IsFiniteMeasure (F.measure.restrict (Icc a b)) := by
  rw [isFiniteMeasure_restrict]
  rw [F.measure_Icc a b]
  exact ENNReal.ofReal_ne_top
