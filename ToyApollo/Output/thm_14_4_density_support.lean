import Mathlib
import ToyApollo.Output.def_8_5
import ToyApollo.Output.thm_14_4_dominating_measure

/-
Parent-owned density support for Theorem 14.4.  The main theorem in
`thm_14_4.lean` keeps the source-facing statement; this file supplies the
Radon-Nikodym density and total-variation estimates used in the textbook proof.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- The quantitative estimate used in Theorem 14.4 after writing
`ν_n = (μ_n + μ) / 2` and representing both measures by RN densities. -/
def thm_14_4_boundedContinuousTestDifferenceBound
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ) : Prop :=
  ∀ n : ℕ, ∀ h : BoundedContinuousFunction ℝ ℝ,
    |(∫ x, h x ∂(Pseq n : Measure ℝ)) - ∫ x, h x ∂(P : Measure ℝ)| ≤
      (2 * ‖h‖) * totalVariationDistance (Pseq n : Measure ℝ) (P : Measure ℝ)

/-- A measure built from a real density with respect to an arbitrary base
measure. -/
def thm_14_4_densityMeasure
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (f : α → ℝ) : Measure α :=
  ν.withDensity fun x => ENNReal.ofReal (f x)

/-- Pointwise difference of two real densities. -/
def thm_14_4_densityDiff {α : Type*} (f g : α → ℝ) (x : α) : ℝ :=
  f x - g x

/-- Positive part of the density difference. -/
def thm_14_4_densityPos {α : Type*} (f g : α → ℝ) (x : α) : ℝ :=
  max (thm_14_4_densityDiff f g x) 0

/-- The maximizing event in the density proof of the total variation formula. -/
def thm_14_4_densityPositiveSet {α : Type*} (f g : α → ℝ) : Set α :=
  {x | 0 < thm_14_4_densityDiff f g x}

lemma thm_14_4_densityMeasure_real_apply
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → ℝ} (hf_int : Integrable f ν) (hf_nonneg : ∀ x, 0 ≤ f x)
    (s : Set α) (hs : MeasurableSet s) :
    (thm_14_4_densityMeasure ν f).real s = ∫ x in s, f x ∂ν := by
  rw [thm_14_4_densityMeasure, Measure.real_def, withDensity_apply _ hs]
  have h_int : Integrable f (ν.restrict s) := hf_int.restrict
  have h_nonneg : 0 ≤ᵐ[ν.restrict s] f := Filter.Eventually.of_forall hf_nonneg
  have hEq :
      ENNReal.ofReal (∫ x in s, f x ∂ν) = ∫⁻ x in s, ENNReal.ofReal (f x) ∂ν := by
    simpa using MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg
  have hint_nonneg : 0 ≤ ∫ x in s, f x ∂ν := by
    exact MeasureTheory.integral_nonneg fun x => hf_nonneg x
  simpa [ENNReal.toReal_ofReal hint_nonneg] using (congrArg ENNReal.toReal hEq).symm

lemma thm_14_4_densityMeasure_apply_univ
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → ℝ} (hf_int : Integrable f ν) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_prob : ∫ x, f x ∂ν = 1) :
    thm_14_4_densityMeasure ν f Set.univ = 1 := by
  rw [thm_14_4_densityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have h_nonneg : 0 ≤ᵐ[ν] f := Filter.Eventually.of_forall hf_nonneg
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf_int h_nonneg, hf_prob]
  norm_num

lemma thm_14_4_densityMeasure_real_compl_eq_one_sub
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f : α → ℝ} (hf_int : Integrable f ν) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_prob : ∫ x, f x ∂ν = 1) (s : Set α) (hs : MeasurableSet s) :
    (thm_14_4_densityMeasure ν f).real sᶜ =
      1 - (thm_14_4_densityMeasure ν f).real s := by
  have hsum :
      thm_14_4_densityMeasure ν f s + thm_14_4_densityMeasure ν f sᶜ = 1 := by
    calc
      thm_14_4_densityMeasure ν f s + thm_14_4_densityMeasure ν f sᶜ =
          thm_14_4_densityMeasure ν f Set.univ := by
            simpa using
              (measure_add_measure_compl (μ := thm_14_4_densityMeasure ν f) hs)
      _ = 1 := thm_14_4_densityMeasure_apply_univ hf_int hf_nonneg hf_prob
  have hs_ne_top : thm_14_4_densityMeasure ν f s ≠ ⊤ := by
    intro hs_top
    rw [hs_top, top_add] at hsum
    simp at hsum
  have hsc_ne_top : thm_14_4_densityMeasure ν f sᶜ ≠ ⊤ := by
    intro hsc_top
    rw [hsc_top, add_top] at hsum
    simp at hsum
  have hreal :
      (thm_14_4_densityMeasure ν f).real s +
        (thm_14_4_densityMeasure ν f).real sᶜ = 1 := by
    simpa [Measure.real_def, ENNReal.toReal_add, hs_ne_top, hsc_ne_top] using
      congrArg ENNReal.toReal hsum
  linarith

lemma thm_14_4_densityDiff_measurable
    {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g) :
    Measurable (thm_14_4_densityDiff f g) := by
  simpa [thm_14_4_densityDiff] using hf_meas.sub hg_meas

lemma thm_14_4_densityPositiveSet_measurable
    {α : Type*} [MeasurableSpace α] {f g : α → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g) :
    MeasurableSet (thm_14_4_densityPositiveSet f g) := by
  have hdiff : Measurable (thm_14_4_densityDiff f g) :=
    thm_14_4_densityDiff_measurable hf_meas hg_meas
  simpa [thm_14_4_densityPositiveSet] using measurableSet_lt measurable_const hdiff

lemma thm_14_4_densityPos_eq_half_abs_add
    {α : Type*} {f g : α → ℝ} (x : α) :
    thm_14_4_densityPos f g x =
      (|thm_14_4_densityDiff f g x| + thm_14_4_densityDiff f g x) / 2 := by
  by_cases hx : 0 ≤ thm_14_4_densityDiff f g x
  · rw [thm_14_4_densityPos, max_eq_left hx, abs_of_nonneg hx]
    ring
  · have hx' : thm_14_4_densityDiff f g x < 0 := lt_of_not_ge hx
    rw [thm_14_4_densityPos, max_eq_right (le_of_lt hx'), abs_of_neg hx']
    ring

lemma thm_14_4_integrable_densityPos
    {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hf_int : Integrable f ν) (hg_int : Integrable g ν) :
    Integrable (thm_14_4_densityPos f g) ν := by
  have hdiff : Integrable (thm_14_4_densityDiff f g) ν := by
    simpa [thm_14_4_densityDiff] using hf_int.sub hg_int
  have habs : Integrable (fun x => |thm_14_4_densityDiff f g x|) ν := hdiff.norm
  have hadd :
      Integrable (fun x => |thm_14_4_densityDiff f g x| +
        thm_14_4_densityDiff f g x) ν := habs.add hdiff
  have hformula :
      thm_14_4_densityPos f g =
        fun x => (|thm_14_4_densityDiff f g x| +
          thm_14_4_densityDiff f g x) / 2 := by
    funext x
    exact thm_14_4_densityPos_eq_half_abs_add x
  rw [hformula]
  exact hadd.div_const 2

lemma thm_14_4_densityPositiveSet_indicator_eq_pos
    {α : Type*} {f g : α → ℝ} :
    (thm_14_4_densityPositiveSet f g).indicator (thm_14_4_densityDiff f g) =
      thm_14_4_densityPos f g := by
  funext x
  by_cases hx : 0 < thm_14_4_densityDiff f g x
  · simp [thm_14_4_densityPositiveSet, Set.indicator_of_mem, hx,
      thm_14_4_densityPos, le_of_lt hx]
  · have hx' : thm_14_4_densityDiff f g x ≤ 0 := le_of_not_gt hx
    simp [thm_14_4_densityPositiveSet, hx, thm_14_4_densityPos, hx']

lemma thm_14_4_densityMeasure_real_diff_eq_integral_indicator
    {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hf_int : Integrable f ν) (hg_int : Integrable g ν)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (s : Set α) (hs : MeasurableSet s) :
    (thm_14_4_densityMeasure ν f).real s - (thm_14_4_densityMeasure ν g).real s =
      ∫ x, s.indicator (thm_14_4_densityDiff f g) x ∂ν := by
  calc
    (thm_14_4_densityMeasure ν f).real s -
        (thm_14_4_densityMeasure ν g).real s =
        (∫ x in s, f x ∂ν) - ∫ x in s, g x ∂ν := by
          rw [thm_14_4_densityMeasure_real_apply hf_int hf_nonneg s hs,
            thm_14_4_densityMeasure_real_apply hg_int hg_nonneg s hs]
    _ = (∫ x, s.indicator f x ∂ν) - ∫ x, s.indicator g x ∂ν := by
          rw [← integral_indicator hs, ← integral_indicator hs]
    _ = ∫ x, (s.indicator f x - s.indicator g x) ∂ν := by
          symm
          exact MeasureTheory.integral_sub (hf_int.indicator hs) (hg_int.indicator hs)
    _ = ∫ x, s.indicator (thm_14_4_densityDiff f g) x ∂ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall ?_)
          intro x
          by_cases hx : x ∈ s <;>
            simp [hx, thm_14_4_densityDiff]

lemma thm_14_4_densityDiff_indicator_le_pos
    {α : Type*} {f g : α → ℝ} (s : Set α) :
    ∀ x, s.indicator (thm_14_4_densityDiff f g) x ≤ thm_14_4_densityPos f g x := by
  intro x
  by_cases hx : x ∈ s
  · simp [hx, thm_14_4_densityPos]
  · simp [hx, thm_14_4_densityPos]

lemma thm_14_4_densityDiff_le_integral_pos
    {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hf_int : Integrable f ν) (hg_int : Integrable g ν)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (s : Set α) (hs : MeasurableSet s) :
    (thm_14_4_densityMeasure ν f).real s -
        (thm_14_4_densityMeasure ν g).real s ≤
      ∫ x, thm_14_4_densityPos f g x ∂ν := by
  rw [thm_14_4_densityMeasure_real_diff_eq_integral_indicator
    hf_int hg_int hf_nonneg hg_nonneg s hs]
  exact MeasureTheory.integral_mono_ae
    ((hf_int.sub hg_int).indicator hs)
    (thm_14_4_integrable_densityPos hf_int hg_int)
    (Filter.Eventually.of_forall (thm_14_4_densityDiff_indicator_le_pos s))

lemma thm_14_4_densityPos_integral_eq_half_abs
    {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hf_int : Integrable f ν) (hg_int : Integrable g ν)
    (hf_prob : ∫ x, f x ∂ν = 1) (hg_prob : ∫ x, g x ∂ν = 1) :
    ∫ x, thm_14_4_densityPos f g x ∂ν =
      (1 / 2 : ℝ) * ∫ x, |thm_14_4_densityDiff f g x| ∂ν := by
  have hdiff : Integrable (thm_14_4_densityDiff f g) ν := by
    simpa [thm_14_4_densityDiff] using hf_int.sub hg_int
  have habs : Integrable (fun x => |thm_14_4_densityDiff f g x|) ν := hdiff.norm
  calc
    ∫ x, thm_14_4_densityPos f g x ∂ν =
        ∫ x, (|thm_14_4_densityDiff f g x| +
          thm_14_4_densityDiff f g x) / 2 ∂ν := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            exact thm_14_4_densityPos_eq_half_abs_add x
    _ = ((∫ x, |thm_14_4_densityDiff f g x| ∂ν) +
          ∫ x, thm_14_4_densityDiff f g x ∂ν) / 2 := by
            rw [MeasureTheory.integral_div 2, MeasureTheory.integral_add habs hdiff]
    _ = ((∫ x, |thm_14_4_densityDiff f g x| ∂ν) +
          ((∫ x, f x ∂ν) - ∫ x, g x ∂ν)) / 2 := by
            have hsub :
                ∫ x, thm_14_4_densityDiff f g x ∂ν =
                  (∫ x, f x ∂ν) - ∫ x, g x ∂ν := by
              simpa [thm_14_4_densityDiff] using (MeasureTheory.integral_sub hf_int hg_int)
            rw [hsub]
    _ = (1 / 2 : ℝ) * ∫ x, |thm_14_4_densityDiff f g x| ∂ν := by
            rw [hf_prob, hg_prob]
            ring

lemma thm_14_4_densityPositiveSet_real_diff_eq_half_abs
    {α : Type*} [MeasurableSpace α] {ν : Measure α} {f g : α → ℝ}
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f ν) (hg_int : Integrable g ν)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_prob : ∫ x, f x ∂ν = 1) (hg_prob : ∫ x, g x ∂ν = 1) :
    (thm_14_4_densityMeasure ν f).real (thm_14_4_densityPositiveSet f g) -
        (thm_14_4_densityMeasure ν g).real (thm_14_4_densityPositiveSet f g) =
      (1 / 2 : ℝ) * ∫ x, |thm_14_4_densityDiff f g x| ∂ν := by
  rw [thm_14_4_densityMeasure_real_diff_eq_integral_indicator hf_int hg_int
      hf_nonneg hg_nonneg (thm_14_4_densityPositiveSet f g)
      (thm_14_4_densityPositiveSet_measurable hf_meas hg_meas)]
  rw [thm_14_4_densityPositiveSet_indicator_eq_pos]
  exact thm_14_4_densityPos_integral_eq_half_abs hf_int hg_int hf_prob hg_prob

/-- The Chapter 8 density-TV formula, generalized from Lebesgue measure to an
arbitrary dominating measure. -/
theorem thm_14_4_totalVariationDistance_withDensity_eq_half_integral_abs
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {f g : α → ℝ} (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f ν) (hg_int : Integrable g ν)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_prob : ∫ x, f x ∂ν = 1) (hg_prob : ∫ x, g x ∂ν = 1) :
    totalVariationDistance (thm_14_4_densityMeasure ν f) (thm_14_4_densityMeasure ν g) =
      (1 / 2 : ℝ) * ∫ x, |thm_14_4_densityDiff f g x| ∂ν := by
  let S : Set ℝ :=
    {d : ℝ | ∃ A : Set α, MeasurableSet A ∧
      d = |(thm_14_4_densityMeasure ν f).real A -
        (thm_14_4_densityMeasure ν g).real A|}
  have hnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨∅, MeasurableSet.empty, ?_⟩
    simp
  have hupper :
      ∀ d ∈ S, d ≤ (1 / 2 : ℝ) *
        ∫ x, |thm_14_4_densityDiff f g x| ∂ν := by
    intro d hd
    rcases hd with ⟨A, hA, rfl⟩
    let δ :=
      (thm_14_4_densityMeasure ν f).real A -
        (thm_14_4_densityMeasure ν g).real A
    by_cases hδ : 0 ≤ δ
    · rw [abs_of_nonneg hδ]
      exact (thm_14_4_densityDiff_le_integral_pos
        hf_int hg_int hf_nonneg hg_nonneg A hA).trans_eq
        (thm_14_4_densityPos_integral_eq_half_abs hf_int hg_int hf_prob hg_prob)
    · have hδ' : δ < 0 := lt_of_not_ge hδ
      have hcomp :
          |δ| =
            (thm_14_4_densityMeasure ν f).real Aᶜ -
              (thm_14_4_densityMeasure ν g).real Aᶜ := by
        rw [abs_of_neg hδ']
        rw [thm_14_4_densityMeasure_real_compl_eq_one_sub hf_int hf_nonneg hf_prob A hA,
          thm_14_4_densityMeasure_real_compl_eq_one_sub hg_int hg_nonneg hg_prob A hA]
        dsimp [δ]
        ring
      rw [hcomp]
      exact (thm_14_4_densityDiff_le_integral_pos
        hf_int hg_int hf_nonneg hg_nonneg Aᶜ hA.compl).trans_eq
        (thm_14_4_densityPos_integral_eq_half_abs hf_int hg_int hf_prob hg_prob)
  have hbounded : BddAbove S :=
    ⟨(1 / 2 : ℝ) * ∫ x, |thm_14_4_densityDiff f g x| ∂ν, hupper⟩
  have hlower :
      (1 / 2 : ℝ) * ∫ x, |thm_14_4_densityDiff f g x| ∂ν ≤
        totalVariationDistance (thm_14_4_densityMeasure ν f)
          (thm_14_4_densityMeasure ν g) := by
    unfold totalVariationDistance
    have hnonnegA :
        0 ≤
          (thm_14_4_densityMeasure ν f).real (thm_14_4_densityPositiveSet f g) -
            (thm_14_4_densityMeasure ν g).real (thm_14_4_densityPositiveSet f g) := by
      rw [thm_14_4_densityPositiveSet_real_diff_eq_half_abs hf_meas hg_meas
        hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob]
      positivity
    have hmem :
        (1 / 2 : ℝ) * ∫ x, |thm_14_4_densityDiff f g x| ∂ν ∈ S := by
      refine ⟨thm_14_4_densityPositiveSet f g,
        thm_14_4_densityPositiveSet_measurable hf_meas hg_meas, ?_⟩
      rw [← thm_14_4_densityPositiveSet_real_diff_eq_half_abs hf_meas hg_meas
        hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob]
      rw [abs_of_nonneg hnonnegA]
    exact le_csSup hbounded hmem
  unfold totalVariationDistance
  apply le_antisymm
  · exact csSup_le hnonempty hupper
  · exact hlower

lemma thm_14_4_rn_densityMeasure_eq
    {α : Type*} [MeasurableSpace α] (P ν : Measure α)
    [SFinite P] [SigmaFinite P] [SigmaFinite ν] (hPν : P ≪ ν) :
    P = thm_14_4_densityMeasure ν (fun x => (P.rnDeriv ν x).toReal) := by
  symm
  rw [thm_14_4_densityMeasure]
  calc
    ν.withDensity (fun x => ENNReal.ofReal (P.rnDeriv ν x).toReal) =
        ν.withDensity (P.rnDeriv ν) := by
          apply withDensity_congr_ae
          filter_upwards [Measure.rnDeriv_lt_top P ν] with x hx
          exact ENNReal.ofReal_toReal hx.ne
    _ = P := Measure.withDensity_rnDeriv_eq P ν hPν

/-- The RN-specialized version of the generalized density-TV formula. -/
theorem thm_14_4_rn_totalVariationDistance_eq_half_integral_abs
    {α : Type*} [MeasurableSpace α] (P Q ν : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure ν]
    (hPν : P ≪ ν) (hQν : Q ≪ ν) :
    totalVariationDistance P Q =
      (1 / 2 : ℝ) *
        ∫ x, |(P.rnDeriv ν x).toReal - (Q.rnDeriv ν x).toReal| ∂ν := by
  let f : α → ℝ := fun x => (P.rnDeriv ν x).toReal
  let g : α → ℝ := fun x => (Q.rnDeriv ν x).toReal
  have hf_meas : Measurable f := by
    dsimp [f]
    exact (Measure.measurable_rnDeriv P ν).ennreal_toReal
  have hg_meas : Measurable g := by
    dsimp [g]
    exact (Measure.measurable_rnDeriv Q ν).ennreal_toReal
  have hf_int : Integrable f ν := by
    dsimp [f]
    exact Measure.integrable_toReal_rnDeriv
  have hg_int : Integrable g ν := by
    dsimp [g]
    exact Measure.integrable_toReal_rnDeriv
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact ENNReal.toReal_nonneg
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    exact ENNReal.toReal_nonneg
  have hf_prob : ∫ x, f x ∂ν = 1 := by
    dsimp [f]
    rw [Measure.integral_toReal_rnDeriv hPν]
    simp [Measure.real_def]
  have hg_prob : ∫ x, g x ∂ν = 1 := by
    dsimp [g]
    rw [Measure.integral_toReal_rnDeriv hQν]
    simp [Measure.real_def]
  have hPdens : P = thm_14_4_densityMeasure ν f := by
    dsimp [f]
    exact thm_14_4_rn_densityMeasure_eq P ν hPν
  have hQdens : Q = thm_14_4_densityMeasure ν g := by
    dsimp [g]
    exact thm_14_4_rn_densityMeasure_eq Q ν hQν
  calc
    totalVariationDistance P Q =
        totalVariationDistance (thm_14_4_densityMeasure ν f)
          (thm_14_4_densityMeasure ν g) := by
          rw [hPdens, hQdens]
    _ = (1 / 2 : ℝ) * ∫ x, |thm_14_4_densityDiff f g x| ∂ν :=
          thm_14_4_totalVariationDistance_withDensity_eq_half_integral_abs
            ν hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob
    _ = (1 / 2 : ℝ) *
        ∫ x, |(P.rnDeriv ν x).toReal - (Q.rnDeriv ν x).toReal| ∂ν := by
          rfl

/-- The triangle-inequality estimate for bounded continuous test functions,
after rewriting both measures by RN densities relative to the same `ν`. -/
theorem thm_14_4_rn_triangle_density_estimate
    (P Q ν : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure ν] (hPν : P ≪ ν) (hQν : Q ≪ ν)
    (h : BoundedContinuousFunction ℝ ℝ) :
    |(∫ x, h x ∂P) - ∫ x, h x ∂Q| ≤
      ‖h‖ * ∫ x, |(P.rnDeriv ν x).toReal - (Q.rnDeriv ν x).toReal| ∂ν := by
  let fp : ℝ → ℝ := fun x => (P.rnDeriv ν x).toReal
  let fq : ℝ → ℝ := fun x => (Q.rnDeriv ν x).toReal
  have hfp_int : Integrable fp ν := by
    dsimp [fp]
    exact Measure.integrable_toReal_rnDeriv
  have hfq_int : Integrable fq ν := by
    dsimp [fq]
    exact Measure.integrable_toReal_rnDeriv
  have hdiff_int : Integrable (fun x => fp x - fq x) ν := hfp_int.sub hfq_int
  have hh_int : Integrable (fun x => h x) ν := h.integrable ν
  have hbound : ∀ᵐ x ∂ν, ‖h x‖ ≤ ‖h‖ :=
    Filter.Eventually.of_forall fun x => h.norm_coe_le_norm x
  have hfp_mul_int : Integrable (fun x => fp x * h x) ν :=
    hfp_int.mul_bdd hh_int.1 hbound
  have hfq_mul_int : Integrable (fun x => fq x * h x) ν :=
    hfq_int.mul_bdd hh_int.1 hbound
  have hdiff_mul_int : Integrable (fun x => (fp x - fq x) * h x) ν :=
    hdiff_int.mul_bdd hh_int.1 hbound
  have hPint : ∫ x, h x ∂P = ∫ x, fp x * h x ∂ν := by
    have hrewrite :=
      integral_rnDeriv_smul (μ := P) (ν := ν) hPν (f := fun x => h x)
    simpa [fp, smul_eq_mul] using hrewrite.symm
  have hQint : ∫ x, h x ∂Q = ∫ x, fq x * h x ∂ν := by
    have hrewrite :=
      integral_rnDeriv_smul (μ := Q) (ν := ν) hQν (f := fun x => h x)
    simpa [fq, smul_eq_mul] using hrewrite.symm
  have hsub :
      (∫ x, h x ∂P) - ∫ x, h x ∂Q =
        ∫ x, (fp x - fq x) * h x ∂ν := by
    rw [hPint, hQint]
    rw [← integral_sub hfp_mul_int hfq_mul_int]
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    ring
  calc
    |(∫ x, h x ∂P) - ∫ x, h x ∂Q| =
        |∫ x, (fp x - fq x) * h x ∂ν| := by rw [hsub]
    _ ≤ ∫ x, |(fp x - fq x) * h x| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x, ‖h‖ * |fp x - fq x| ∂ν := by
      refine integral_mono_ae hdiff_mul_int.norm (hdiff_int.norm.const_mul ‖h‖) ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      have hh : |h x| ≤ ‖h‖ := by
        simpa [Real.norm_eq_abs] using h.norm_coe_le_norm x
      calc
        |(fp x - fq x) * h x| = |fp x - fq x| * |h x| := abs_mul _ _
        _ ≤ |fp x - fq x| * ‖h‖ :=
          mul_le_mul_of_nonneg_left hh (abs_nonneg _)
        _ = ‖h‖ * |fp x - fq x| := by ring
    _ = ‖h‖ * ∫ x, |fp x - fq x| ∂ν := by
      rw [integral_const_mul]
    _ = ‖h‖ *
        ∫ x, |(P.rnDeriv ν x).toReal - (Q.rnDeriv ν x).toReal| ∂ν := by
      rfl

/-- The textbook bound used to pass from TV convergence to convergence of all
bounded continuous test integrals. -/
theorem thm_14_4_boundedContinuousTestDifferenceBound_from_rn
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ) :
    thm_14_4_boundedContinuousTestDifferenceBound Pseq P := by
  intro n h
  let ν : Measure ℝ := thm_14_4_dominatingMeasureSeq Pseq P n
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, thm_14_4_dominatingMeasureSeq]
    infer_instance
  have hPν : (Pseq n : Measure ℝ) ≪ ν := by
    dsimp [ν]
    exact thm_14_4_mu_n_absolutelyContinuous Pseq P n
  have hQν : (P : Measure ℝ) ≪ ν := by
    dsimp [ν]
    exact thm_14_4_mu_absolutelyContinuous Pseq P n
  let I : ℝ :=
    ∫ x, |((Pseq n : Measure ℝ).rnDeriv ν x).toReal -
      ((P : Measure ℝ).rnDeriv ν x).toReal| ∂ν
  have htri :
      |(∫ x, h x ∂(Pseq n : Measure ℝ)) - ∫ x, h x ∂(P : Measure ℝ)| ≤
        ‖h‖ * I := by
    simpa [I] using
      thm_14_4_rn_triangle_density_estimate
        (Pseq n : Measure ℝ) (P : Measure ℝ) ν hPν hQν h
  have htv :
      totalVariationDistance (Pseq n : Measure ℝ) (P : Measure ℝ) =
        (1 / 2 : ℝ) * I := by
    simpa [I] using
      thm_14_4_rn_totalVariationDistance_eq_half_integral_abs
        (Pseq n : Measure ℝ) (P : Measure ℝ) ν hPν hQν
  calc
    |(∫ x, h x ∂(Pseq n : Measure ℝ)) - ∫ x, h x ∂(P : Measure ℝ)|
        ≤ ‖h‖ * I := htri
    _ = (2 * ‖h‖) * totalVariationDistance (Pseq n : Measure ℝ) (P : Measure ℝ) := by
      rw [htv]
      ring
