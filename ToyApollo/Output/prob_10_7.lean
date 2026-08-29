/-
TASK ID: prob_10_7
TYPE: Problem
SOURCE PLAN: chapter10-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_1
import ToyApollo.Output.def_10_2
import ToyApollo.Output.def_10_3
import ToyApollo.Output.thm_5_8
import ToyApollo.Output.thm_10_1

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable def prob_10_7_binaryLaw : Measure ℝ :=
  ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac (-1) +
    ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac 1

noncomputable def prob_10_7_uniformLaw : Measure ℝ :=
  volume.restrict (Icc 0 1)

def prob_10_7_rareEvent {Ω : Type*} (U : ℕ → Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω : Ω | U n ω < 1 / ((n : ℝ) + 1) ^ 2}

noncomputable def rarePerturbationYn {Ω : Type*} (X : Ω → ℝ)
    (U : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  if U n ω < 1 / ((n : ℝ) + 1) ^ 2 then Real.pi * ((n : ℝ) + 1) else X ω

structure Prob_10_7_SourceSetup {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (U : ℕ → Ω → ℝ) : Prop where
  x_measurable : Measurable X
  x_law : ProbabilityTheory.HasLaw X prob_10_7_binaryLaw μ
  u_measurable : ∀ n : ℕ, Measurable (U n)
  u_uniform :
    ∀ n : ℕ, ProbabilityTheory.HasLaw (U n) prob_10_7_uniformLaw μ
  u_independent : ProbabilityTheory.iIndepFun U μ
  x_u_independent :
    ProbabilityTheory.IndepFun X (fun ω n => U n ω) μ

def RarePerturbationAnswer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (U : ℕ → Ω → ℝ) : Prop :=
  ConvergesInProbability μ (rarePerturbationYn X U) X ∧
    ConvergesAlmostSurely μ (rarePerturbationYn X U) X ∧
      ¬ ConvergesInMeanSquare μ (rarePerturbationYn X U) X

private lemma prob_10_7_rare_measurable {Ω : Type*} [MeasurableSpace Ω]
    {U : ℕ → Ω → ℝ} (hU : ∀ n : ℕ, Measurable (U n)) :
    ∀ n : ℕ, MeasurableSet (prob_10_7_rareEvent U n) := by
  intro n
  exact (hU n) measurableSet_Iio

private lemma prob_10_7_rare_probability {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : ℕ → Ω → ℝ}
    (hULaw :
      ∀ n : ℕ, ProbabilityTheory.HasLaw (U n) prob_10_7_uniformLaw μ) :
    ∀ n : ℕ, μ (prob_10_7_rareEvent U n) =
      ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2) := by
  intro n
  let t : ℝ := 1 / ((n : ℝ) + 1) ^ 2
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hden : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have ht_le : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one (by positivity : 0 < ((n : ℝ) + 1) ^ 2)).2 hden
  calc
    μ (prob_10_7_rareEvent U n) = prob_10_7_uniformLaw (Iio t) := by
      change μ {ω | U n ω < t} = prob_10_7_uniformLaw {x | x < t}
      exact (hULaw n).measure_eq (p := fun x : ℝ => x < t) measurableSet_Iio
    _ = volume (Iio t ∩ Icc (0 : ℝ) 1) := by
      rw [prob_10_7_uniformLaw, Measure.restrict_apply measurableSet_Iio]
    _ = volume (Ico (0 : ℝ) t) := by
      congr 1
      ext x
      constructor
      · intro hx
        exact ⟨hx.2.1, hx.1⟩
      · intro hx
        exact ⟨hx.2, hx.1, le_trans hx.2.le ht_le⟩
    _ = ENNReal.ofReal t := by simp [Real.volume_Ico]
    _ = ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2) := by rfl

private lemma prob_10_7_x_binary_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ}
    (hX : ProbabilityTheory.HasLaw X prob_10_7_binaryLaw μ) :
    ∀ᵐ ω ∂μ, X ω = -1 ∨ X ω = 1 := by
  refine (hX.ae_iff (p := fun x : ℝ => x = -1 ∨ x = 1) ?_).2 ?_
  · exact measurableSet_setOf.mp <|
      (measurableSet_singleton (-1 : ℝ)).union (measurableSet_singleton 1)
  · rw [MeasureTheory.ae_iff]
    simp [prob_10_7_binaryLaw]

private lemma prob_10_7_random_variables {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {U : ℕ → Ω → ℝ}
    (hX : Measurable X) (hU : ∀ n : ℕ, Measurable (U n)) :
    (∀ n : ℕ, Measurable (rarePerturbationYn X U n)) ∧ Measurable X := by
  constructor
  · intro n
    exact Measurable.ite ((hU n) measurableSet_Iio) measurable_const hX
  · exact hX

private lemma prob_10_7_deviationEvent_subset_rareEvent {Ω : Type*}
    {X : Ω → ℝ} {U : ℕ → Ω → ℝ} {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    deviationEvent (rarePerturbationYn X U) X n ε ⊆
      prob_10_7_rareEvent U n := by
  intro ω hω
  by_contra hnot
  have heq : rarePerturbationYn X U n ω = X ω := by
    have hcond : ¬ U n ω < 1 / ((n : ℝ) + 1) ^ 2 := by
      simpa [prob_10_7_rareEvent] using hnot
    have hcond' : ¬ U n ω < (((n : ℝ) + 1) ^ 2)⁻¹ := by
      simpa [one_div] using hcond
    simp [rarePerturbationYn, one_div, hcond']
  have hnot_dev :
      ¬ |rarePerturbationYn X U n ω - X ω| > ε := by
    rw [heq]
    simpa using not_lt.mpr hε.le
  exact hnot_dev hω

private lemma prob_10_7_almostSureDeviationEvent_subset_rareEvent {Ω : Type*}
    {X : Ω → ℝ} {U : ℕ → Ω → ℝ} {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    almostSureDeviationEvent (rarePerturbationYn X U) X n ε ⊆
      prob_10_7_rareEvent U n := by
  intro ω hω
  by_contra hnot
  have heq : rarePerturbationYn X U n ω = X ω := by
    have hcond : ¬ U n ω < 1 / ((n : ℝ) + 1) ^ 2 := by
      simpa [prob_10_7_rareEvent] using hnot
    have hcond' : ¬ U n ω < (((n : ℝ) + 1) ^ 2)⁻¹ := by
      simpa [one_div] using hcond
    simp [rarePerturbationYn, one_div, hcond']
  have hnot_dev :
      ¬ |rarePerturbationYn X U n ω - X ω| > ε := by
    rw [heq]
    simpa [almostSureDeviationEvent] using not_lt.mpr hε.le
  exact hnot_dev hω

private lemma prob_10_7_limsup_deviation_subset_rareEvent {Ω : Type*}
    {X : Ω → ℝ} {U : ℕ → Ω → ℝ} {ε : ℝ} (hε : 0 < ε) :
    deviationInfinitelyOften (rarePerturbationYn X U) X ε ⊆
      limsup (fun n : ℕ => prob_10_7_rareEvent U n) atTop := by
  intro ω hω
  change ω ∈ limsup (fun n : ℕ =>
    almostSureDeviationEvent (rarePerturbationYn X U) X n ε) atTop at hω
  rw [mem_limsup_iff_frequently_mem] at hω
  rw [mem_limsup_iff_frequently_mem]
  exact hω.mono fun n hn =>
    prob_10_7_almostSureDeviationEvent_subset_rareEvent hε hn

private lemma prob_10_7_summable_rareProbReal :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have hsumm : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (2 : ℝ)).2 (by norm_num)
  refine hsumm.congr ?_
  intro n
  have hnonneg : 0 ≤ (n : ℝ) + 1 := by positivity
  rw [abs_of_nonneg hnonneg]
  rw [show ((n : ℝ) + 1) ^ (2 : ℝ) = ((n : ℝ) + 1) ^ (2 : ℕ) by
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num]
    exact Real.rpow_natCast ((n : ℝ) + 1) 2]

private lemma prob_10_7_rareProb_tendsto_zero :
    Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2))
      atTop (nhds 0) := by
  simpa using ENNReal.tendsto_ofReal prob_10_7_summable_rareProbReal.tendsto_atTop_zero

private lemma prob_10_7_rareEvent_tsum_ne_top {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {U : ℕ → Ω → ℝ}
    (hRareProb :
      ∀ n : ℕ, μ (prob_10_7_rareEvent U n) =
        ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2)) :
    (∑' n : ℕ, μ (prob_10_7_rareEvent U n)) ≠ ∞ := by
  have hfinite :
      (∑' n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2)) ≠ ∞ :=
    prob_10_7_summable_rareProbReal.tsum_ofReal_ne_top
  simpa [hRareProb] using hfinite

private lemma prob_10_7_convergesInProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (U : ℕ → Ω → ℝ)
    (hXn : ∀ n : ℕ, Measurable (rarePerturbationYn X U n))
    (hX : Measurable X)
    (hRareProb :
      ∀ n : ℕ, μ (prob_10_7_rareEvent U n) =
        ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2)) :
    ConvergesInProbability μ (rarePerturbationYn X U) X := by
  refine ⟨hXn, hX, ?_⟩
  intro ε hε
  have hrare :
      Tendsto (fun n : ℕ => μ (prob_10_7_rareEvent U n)) atTop (nhds 0) := by
    refine prob_10_7_rareProb_tendsto_zero.congr' ?_
    exact Eventually.of_forall fun n => (hRareProb n).symm
  have hle :
      ∀ n : ℕ,
        μ (deviationEvent (rarePerturbationYn X U) X n ε) ≤
          μ (prob_10_7_rareEvent U n) := by
    intro n
    exact measure_mono (prob_10_7_deviationEvent_subset_rareEvent hε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hrare
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall hle)

private lemma prob_10_7_convergesAlmostSurely {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (U : ℕ → Ω → ℝ)
    (hXn : ∀ n : ℕ, AEStronglyMeasurable (rarePerturbationYn X U n) μ)
    (hX : AEStronglyMeasurable X μ)
    (hRareProb :
      ∀ n : ℕ, μ (prob_10_7_rareEvent U n) =
        ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2)) :
    ConvergesAlmostSurely μ (rarePerturbationYn X U) X := by
  have hseries :
      (∑' n : ℕ, μ (prob_10_7_rareEvent U n)) ≠ ∞ :=
    prob_10_7_rareEvent_tsum_ne_top hRareProb
  have hrare_limsup :
      μ (limsup (fun n : ℕ => prob_10_7_rareEvent U n) atTop) = 0 :=
    thm_5_8 (P := μ) (A := fun n : ℕ => prob_10_7_rareEvent U n) hseries
  refine (thm_10_1 μ (rarePerturbationYn X U) X).2 ?_
  refine ⟨hXn, hX, ?_⟩
  intro ε hε
  exact MeasureTheory.measure_mono_null
    (prob_10_7_limsup_deviation_subset_rareEvent hε) hrare_limsup

private lemma prob_10_7_abs_deviation_lower {Ω : Type*}
    {X : Ω → ℝ} {U : ℕ → Ω → ℝ}
    {n : ℕ} {ω : Ω} (hBinary : X ω = -1 ∨ X ω = 1)
    (hω : ω ∈ prob_10_7_rareEvent U n) :
    ((n : ℝ) + 1) ≤ |rarePerturbationYn X U n ω - X ω| := by
  have hY : rarePerturbationYn X U n ω = Real.pi * ((n : ℝ) + 1) := by
    have hcond : U n ω < 1 / ((n : ℝ) + 1) ^ 2 := by
      simpa [prob_10_7_rareEvent] using hω
    have hcond' : U n ω < (((n : ℝ) + 1) ^ 2)⁻¹ := by
      simpa [one_div] using hcond
    simp [rarePerturbationYn, one_div, hcond']
  have hNpos : 0 < (n : ℝ) + 1 := by positivity
  have hNge_one : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rcases hBinary with hx | hx
  · rw [hY, hx]
    have hinside_nonneg : 0 ≤ Real.pi * ((n : ℝ) + 1) - (-1 : ℝ) := by
      nlinarith [Real.pi_pos, hNpos]
    rw [abs_of_nonneg hinside_nonneg]
    nlinarith [Real.two_le_pi, hNpos]
  · rw [hY, hx]
    have hinside_nonneg : 0 ≤ Real.pi * ((n : ℝ) + 1) - (1 : ℝ) := by
      nlinarith [Real.two_le_pi, hNge_one]
    rw [abs_of_nonneg hinside_nonneg]
    nlinarith [Real.two_le_pi, hNge_one]

private lemma prob_10_7_square_deviation_lower {Ω : Type*}
    {X : Ω → ℝ} {U : ℕ → Ω → ℝ}
    {n : ℕ} {ω : Ω} (hBinary : X ω = -1 ∨ X ω = 1)
    (hω : ω ∈ prob_10_7_rareEvent U n) :
    ENNReal.ofReal (((n : ℝ) + 1) ^ 2) ≤
      ENNReal.ofReal (|rarePerturbationYn X U n ω - X ω| ^ (2 : ℝ)) := by
  refine ENNReal.ofReal_le_ofReal ?_
  have hAbs := prob_10_7_abs_deviation_lower hBinary hω
  have hNnonneg : 0 ≤ (n : ℝ) + 1 := by positivity
  have hsq :
      ((n : ℝ) + 1) ^ (2 : ℕ) ≤
        |rarePerturbationYn X U n ω - X ω| ^ (2 : ℕ) :=
    pow_le_pow_left₀ hNnonneg hAbs 2
  simpa [Real.rpow_natCast] using hsq

private lemma prob_10_7_meanSquareMoment_lower_bound {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (U : ℕ → Ω → ℝ)
    (hBinary : ∀ᵐ ω ∂μ, X ω = -1 ∨ X ω = 1)
    (hRareMeas : ∀ n : ℕ, MeasurableSet (prob_10_7_rareEvent U n))
    (hRareProb :
      ∀ n : ℕ, μ (prob_10_7_rareEvent U n) =
        ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2))
    (n : ℕ) :
    (1 : ENNReal) ≤ meanDeviationMoment μ (rarePerturbationYn X U) X 2 n := by
  let E : Set Ω := prob_10_7_rareEvent U n
  let c : ENNReal := ENNReal.ofReal (((n : ℝ) + 1) ^ 2)
  have hpoint :
      ∀ᵐ ω : Ω ∂μ,
        E.indicator (fun _ => c) ω ≤
          ENNReal.ofReal (|rarePerturbationYn X U n ω - X ω| ^ (2 : ℝ)) := by
    filter_upwards [hBinary] with ω hXω
    by_cases hω : ω ∈ E
    · have hlow := prob_10_7_square_deviation_lower (U := U) hXω hω
      simpa [E, c, hω] using hlow
    · simp [E, c, hω]
  have hlower :
      c * μ E ≤ meanDeviationMoment μ (rarePerturbationYn X U) X 2 n := by
    calc
      c * μ E =
          ∫⁻ ω, E.indicator (fun _ => c) ω ∂μ := by
            rw [lintegral_indicator_const (hRareMeas n)]
      _ ≤ meanDeviationMoment μ (rarePerturbationYn X U) X 2 n := by
            simpa [meanDeviationMoment] using lintegral_mono_ae hpoint
  have hprod : c * μ E = (1 : ENNReal) := by
    have hNpos : 0 < (n : ℝ) + 1 := by positivity
    have hN2pos : 0 < ((n : ℝ) + 1) ^ 2 := sq_pos_of_pos hNpos
    have hN2ne : ((n : ℝ) + 1) ^ 2 ≠ 0 := ne_of_gt hN2pos
    rw [hRareProb n]
    change
      ENNReal.ofReal (((n : ℝ) + 1) ^ 2) *
          ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2) = (1 : ENNReal)
    rw [← ENNReal.ofReal_mul (by positivity :
      0 ≤ ((n : ℝ) + 1) ^ 2)]
    have hreal : ((n : ℝ) + 1) ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) = 1 := by
      field_simp [hN2ne]
    rw [hreal]
    norm_num
  simpa [hprod] using hlower

private lemma prob_10_7_not_tendsto_zero_of_one_le {f : ℕ → ENNReal}
    (h : ∀ n : ℕ, (1 : ENNReal) ≤ f n) :
    ¬ Tendsto f atTop (nhds 0) := by
  intro ht
  have hsmall : ∀ᶠ n : ℕ in atTop, f n ≤ (1 / 2 : ENNReal) :=
    (ENNReal.tendsto_nhds_zero.mp ht) (1 / 2 : ENNReal) (by norm_num)
  rcases eventually_atTop.1 hsmall with ⟨N, hN⟩
  have hbad : (1 : ENNReal) ≤ 1 / 2 := le_trans (h N) (hN N le_rfl)
  norm_num at hbad

private lemma prob_10_7_not_convergesInMeanSquare {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (U : ℕ → Ω → ℝ)
    (hBinary : ∀ᵐ ω ∂μ, X ω = -1 ∨ X ω = 1)
    (hRareMeas : ∀ n : ℕ, MeasurableSet (prob_10_7_rareEvent U n))
    (hRareProb :
      ∀ n : ℕ, μ (prob_10_7_rareEvent U n) =
        ENNReal.ofReal (1 / ((n : ℝ) + 1) ^ 2)) :
    ¬ ConvergesInMeanSquare μ (rarePerturbationYn X U) X := by
  intro hms
  rw [ConvergesInMeanSquare, ConvergesInRthMean] at hms
  exact prob_10_7_not_tendsto_zero_of_one_le
    (f := fun n : ℕ => meanDeviationMoment μ (rarePerturbationYn X U) X 2 n)
    (fun n => prob_10_7_meanSquareMoment_lower_bound μ X U
      hBinary hRareMeas hRareProb n) hms.2.2.2

theorem prob_10_7 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (U : ℕ → Ω → ℝ)
    (hSetup : Prob_10_7_SourceSetup μ X U) :
    RarePerturbationAnswer μ X U := by
  have hRareMeas := prob_10_7_rare_measurable hSetup.u_measurable
  have hRareProb := prob_10_7_rare_probability hSetup.u_uniform
  have hXBinary := prob_10_7_x_binary_ae hSetup.x_law
  have hRandomVariables :=
    prob_10_7_random_variables (μ := μ) hSetup.x_measurable hSetup.u_measurable
  refine ⟨?_, ?_, ?_⟩
  · exact prob_10_7_convergesInProbability μ X U hRandomVariables.1
      hRandomVariables.2 hRareProb
  · exact prob_10_7_convergesAlmostSurely μ X U
      (fun n => (hRandomVariables.1 n).aestronglyMeasurable)
      hRandomVariables.2.aestronglyMeasurable hRareProb
  · exact prob_10_7_not_convergesInMeanSquare μ X U hXBinary
      hRareMeas hRareProb
