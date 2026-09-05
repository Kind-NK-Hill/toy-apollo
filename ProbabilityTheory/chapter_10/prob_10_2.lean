/-
TASK ID: prob_10_2
TYPE: Problem
SOURCE PLAN: chapter10-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_1
import ProbabilityTheory.chapter_10.def_10_2
import ProbabilityTheory.chapter_05.thm_5_8
import ProbabilityTheory.chapter_05.thm_5_9
import ProbabilityTheory.chapter_10.thm_10_1




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped ENNReal Topology

 
def BernoulliZeroOneMasses {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (p : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, μ {ω : Ω | Xn n ω = 1} = ENNReal.ofReal (p n)) ∧
    (∀ n : ℕ, μ {ω : Ω | Xn n ω = 0} = ENNReal.ofReal (1 - p n))

private lemma prob_10_2_deviationEvent_subset_success {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} {n : ℕ} {ε : ℝ}
    (hBinary : ∀ n : ℕ, ∀ ω : Ω, Xn n ω = 0 ∨ Xn n ω = 1)
    (hε : 0 < ε) :
    deviationEvent Xn (fun _ => 0) n ε ⊆ {ω : Ω | Xn n ω = 1} := by
  intro ω hω
  rcases hBinary n ω with hzero | hone
  · exfalso
    have hnot : ¬ |Xn n ω - (0 : ℝ)| > ε := by
      rw [hzero]
      simpa using not_lt.mpr hε.le
    exact hnot hω
  · exact hone

private lemma prob_10_2_almostSureDeviationEvent_subset_success {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} {n : ℕ} {ε : ℝ}
    (hBinary : ∀ n : ℕ, ∀ ω : Ω, Xn n ω = 0 ∨ Xn n ω = 1)
    (hε : 0 < ε) :
    almostSureDeviationEvent Xn (fun _ => 0) n ε ⊆
      {ω : Ω | Xn n ω = 1} := by
  intro ω hω
  rcases hBinary n ω with hzero | hone
  · exfalso
    have hnot : ¬ |Xn n ω - (0 : ℝ)| > ε := by
      rw [hzero]
      simpa [almostSureDeviationEvent] using not_lt.mpr hε.le
    exact hnot hω
  · exact hone

private lemma prob_10_2_success_subset_deviationEvent_half {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} {n : ℕ} :
    {ω : Ω | Xn n ω = 1} ⊆ deviationEvent Xn (fun _ => 0) n (1 / 2 : ℝ) := by
  intro ω hω
  change |Xn n ω - (0 : ℝ)| > (1 / 2 : ℝ)
  rw [hω]
  norm_num

private lemma prob_10_2_success_subset_almostSureDeviationEvent_half {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} {n : ℕ} :
    {ω : Ω | Xn n ω = 1} ⊆
      almostSureDeviationEvent Xn (fun _ => 0) n (1 / 2 : ℝ) := by
  intro ω hω
  change |Xn n ω - (0 : ℝ)| > (1 / 2 : ℝ)
  rw [hω]
  norm_num

private lemma prob_10_2_deviationEvent_half_eq_success {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} {n : ℕ}
    (hBinary : ∀ n : ℕ, ∀ ω : Ω, Xn n ω = 0 ∨ Xn n ω = 1) :
    deviationEvent Xn (fun _ => 0) n (1 / 2 : ℝ) =
      {ω : Ω | Xn n ω = 1} := by
  apply Set.Subset.antisymm
  · exact prob_10_2_deviationEvent_subset_success hBinary (by norm_num)
  · exact prob_10_2_success_subset_deviationEvent_half

private lemma prob_10_2_limsup_deviation_subset_success {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} {ε : ℝ}
    (hBinary : ∀ n : ℕ, ∀ ω : Ω, Xn n ω = 0 ∨ Xn n ω = 1)
    (hε : 0 < ε) :
    deviationInfinitelyOften Xn (fun _ => 0) ε ⊆
      limsup (fun n : ℕ => {ω : Ω | Xn n ω = 1}) atTop := by
  intro ω hω
  change ω ∈ limsup (fun n : ℕ =>
    almostSureDeviationEvent Xn (fun _ => 0) n ε) atTop at hω
  rw [mem_limsup_iff_frequently_mem] at hω
  rw [mem_limsup_iff_frequently_mem]
  exact hω.mono fun n hn =>
    prob_10_2_almostSureDeviationEvent_subset_success hBinary hε hn

private lemma prob_10_2_limsup_success_subset_deviation_half {Ω : Type*}
    {Xn : ℕ → Ω → ℝ} :
    limsup (fun n : ℕ => {ω : Ω | Xn n ω = 1}) atTop ⊆
      deviationInfinitelyOften Xn (fun _ => 0) (1 / 2 : ℝ) := by
  intro ω hω
  rw [mem_limsup_iff_frequently_mem] at hω
  change ω ∈ limsup (fun n : ℕ =>
    almostSureDeviationEvent Xn (fun _ => 0) n (1 / 2 : ℝ)) atTop
  rw [mem_limsup_iff_frequently_mem]
  exact hω.mono fun n hn =>
    prob_10_2_success_subset_almostSureDeviationEvent_half hn

private lemma prob_10_2_tendsto_ofReal_zero_iff {p : ℕ → ℝ}
    (hp_nonneg : ∀ n : ℕ, 0 ≤ p n) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (p n)) atTop (nhds 0) ↔
      Tendsto p atTop (nhds 0) := by
  constructor
  · intro h
    have h_toReal :
        Tendsto (fun n : ℕ => (ENNReal.ofReal (p n)).toReal) atTop (nhds 0) :=
      (ENNReal.tendsto_toReal_zero_iff
        (f := fun n : ℕ => ENNReal.ofReal (p n))
        (fi := atTop)
        (by intro n; exact ENNReal.ofReal_ne_top)).2 h
    have heq :
        (fun n : ℕ => (ENNReal.ofReal (p n)).toReal) = p := by
      funext n
      exact ENNReal.toReal_ofReal (hp_nonneg n)
    simpa [heq] using h_toReal
  · intro h
    simpa using ENNReal.tendsto_ofReal h

private lemma prob_10_2_summable_iff_tsum_ofReal_ne_top {p : ℕ → ℝ}
    (hp_nonneg : ∀ n : ℕ, 0 ≤ p n) :
    Summable p ↔ (∑' n : ℕ, ENNReal.ofReal (p n)) ≠ ∞ := by
  constructor
  · intro hs
    exact hs.tsum_ofReal_ne_top
  · intro hfinite
    have hs_toReal :
        Summable fun n : ℕ => (ENNReal.ofReal (p n)).toReal :=
      ENNReal.summable_toReal hfinite
    have heq :
        (fun n : ℕ => (ENNReal.ofReal (p n)).toReal) = p := by
      funext n
      exact ENNReal.toReal_ofReal (hp_nonneg n)
    simpa [heq] using hs_toReal

private lemma prob_10_2_tsum_ofReal_eq_top_of_not_summable {p : ℕ → ℝ}
    (hp_nonneg : ∀ n : ℕ, 0 ≤ p n) (hnot : ¬ Summable p) :
    (∑' n : ℕ, ENNReal.ofReal (p n)) = ∞ := by
  by_contra hne
  exact hnot ((prob_10_2_summable_iff_tsum_ofReal_ne_top hp_nonneg).2 hne)

private lemma prob_10_2_convergesInProbability_iff_tendsto_p
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (p : ℕ → ℝ)
    (hXn : ∀ n : ℕ, Measurable (Xn n))
    (hp_nonneg : ∀ n : ℕ, 0 ≤ p n)
    (hBinary : ∀ n : ℕ, ∀ ω : Ω, Xn n ω = 0 ∨ Xn n ω = 1)
    (hBernoulli : BernoulliZeroOneMasses μ Xn p) :
    ConvergesInProbability μ Xn (fun _ => 0) ↔
      Tendsto p atTop (nhds 0) := by
  let A : ℕ → Set Ω := fun n => {ω : Ω | Xn n ω = 1}
  have hprob_one : ∀ n : ℕ, μ (A n) = ENNReal.ofReal (p n) := hBernoulli.1
  constructor
  · intro hconv
    have hdev :
        Tendsto (fun n : ℕ =>
          μ (deviationEvent Xn (fun _ => 0) n (1 / 2 : ℝ))) atTop (nhds 0) :=
      hconv.2.2 (1 / 2 : ℝ) (by norm_num)
    have hsuccess :
        Tendsto (fun n : ℕ => μ (A n)) atTop (nhds 0) := by
      refine hdev.congr' ?_
      exact Eventually.of_forall fun n => by
        change μ (deviationEvent Xn (fun _ => 0) n (1 / 2 : ℝ)) = μ (A n)
        rw [prob_10_2_deviationEvent_half_eq_success (Xn := Xn) hBinary]
    have hofReal :
        Tendsto (fun n : ℕ => ENNReal.ofReal (p n)) atTop (nhds 0) := by
      refine hsuccess.congr' ?_
      exact Eventually.of_forall fun n => by
        change μ (A n) = ENNReal.ofReal (p n)
        exact hprob_one n
    exact (prob_10_2_tendsto_ofReal_zero_iff hp_nonneg).1 hofReal
  · intro hp_tend
    refine ⟨hXn, measurable_const, ?_⟩
    intro ε hε
    have hofReal :
        Tendsto (fun n : ℕ => ENNReal.ofReal (p n)) atTop (nhds 0) :=
      (prob_10_2_tendsto_ofReal_zero_iff hp_nonneg).2 hp_tend
    have hsuccess :
        Tendsto (fun n : ℕ => μ (A n)) atTop (nhds 0) := by
      refine hofReal.congr' ?_
      exact Eventually.of_forall fun n => by
        change ENNReal.ofReal (p n) = μ (A n)
        exact (hprob_one n).symm
    have hle :
        ∀ n : ℕ,
          μ (deviationEvent Xn (fun _ => 0) n ε) ≤ μ (A n) := by
      intro n
      exact measure_mono
        (prob_10_2_deviationEvent_subset_success (Xn := Xn) hBinary hε)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsuccess
      (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall hle)

private lemma prob_10_2_success_measure_tsum_ne_top_iff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (p : ℕ → ℝ)
    (hp_nonneg : ∀ n : ℕ, 0 ≤ p n)
    (hBernoulli : BernoulliZeroOneMasses μ Xn p) :
    Summable p ↔
      (∑' n : ℕ, μ {ω : Ω | Xn n ω = 1}) ≠ ∞ := by
  have hprob_one : ∀ n : ℕ,
      μ {ω : Ω | Xn n ω = 1} = ENNReal.ofReal (p n) := hBernoulli.1
  constructor
  · intro hs
    have hfinite :
        (∑' n : ℕ, ENNReal.ofReal (p n)) ≠ ∞ :=
      (prob_10_2_summable_iff_tsum_ofReal_ne_top hp_nonneg).1 hs
    simpa [hprob_one] using hfinite
  · intro hfinite
    have hfinite' :
        (∑' n : ℕ, ENNReal.ofReal (p n)) ≠ ∞ := by
      simpa [hprob_one] using hfinite
    exact (prob_10_2_summable_iff_tsum_ofReal_ne_top hp_nonneg).2 hfinite'

private lemma prob_10_2_convergesAlmostSurely_iff_summable_p
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ) (p : ℕ → ℝ)
    (hXn : ∀ n : ℕ, AEStronglyMeasurable (Xn n) μ)
    (hp_nonneg : ∀ n : ℕ, 0 ≤ p n)
    (hBinary : ∀ n : ℕ, ∀ ω : Ω, Xn n ω = 0 ∨ Xn n ω = 1)
    (hMeasOne : ∀ n : ℕ, MeasurableSet {ω : Ω | Xn n ω = 1})
    (hBernoulli : BernoulliZeroOneMasses μ Xn p)
    (hIndependent :
      ProbabilityTheory.iIndepSet (fun n : ℕ => {ω : Ω | Xn n ω = 1}) μ) :
    ConvergesAlmostSurely μ Xn (fun _ => 0) ↔ Summable p := by
  let A : ℕ → Set Ω := fun n => {ω : Ω | Xn n ω = 1}
  have hprob_one : ∀ n : ℕ, μ (A n) = ENNReal.ofReal (p n) := hBernoulli.1
  constructor
  · intro hAS
    have hdev_zero :
        μ (deviationInfinitelyOften Xn (fun _ => 0) (1 / 2 : ℝ)) = 0 :=
      ((thm_10_1 μ Xn (fun _ => 0)).1 hAS).2.2 (1 / 2 : ℝ) (by norm_num)
    have hsuccess_zero :
        μ (limsup A atTop) = 0 :=
      MeasureTheory.measure_mono_null
        (prob_10_2_limsup_success_subset_deviation_half (Xn := Xn)) hdev_zero
    by_contra hnot
    have hseries_top :
        (∑' n : ℕ, μ (A n)) = ∞ := by
      have htop :
          (∑' n : ℕ, ENNReal.ofReal (p n)) = ∞ :=
        prob_10_2_tsum_ofReal_eq_top_of_not_summable hp_nonneg hnot
      simpa [hprob_one] using htop
    have hone : μ (limsup A atTop) = 1 :=
      thm_5_9 (P := μ) (A := A)
        (by intro n; exact hMeasOne n) hIndependent hseries_top
    rw [hone] at hsuccess_zero
    exact one_ne_zero hsuccess_zero
  · intro hs
    have hseries_ne_top :
        (∑' n : ℕ, μ (A n)) ≠ ∞ := by
      have hfinite :
          (∑' n : ℕ, ENNReal.ofReal (p n)) ≠ ∞ :=
        (prob_10_2_summable_iff_tsum_ofReal_ne_top hp_nonneg).1 hs
      simpa [hprob_one] using hfinite
    have hsuccess_limsup_zero : μ (limsup A atTop) = 0 :=
      thm_5_8 (P := μ) (A := A) hseries_ne_top
    refine (thm_10_1 μ Xn (fun _ => 0)).2 ?_
    refine ⟨hXn, aestronglyMeasurable_const, ?_⟩
    intro ε hε
    exact MeasureTheory.measure_mono_null
      (prob_10_2_limsup_deviation_subset_success (Xn := Xn) hBinary hε)
      hsuccess_limsup_zero



theorem prob_10_2 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ) (p : ℕ → ℝ)
    (hXn : ∀ n : ℕ, Measurable (Xn n))
    (hp : ∀ n : ℕ, p n ∈ Set.Icc (0 : ℝ) 1)
    (hBinary : ∀ n : ℕ, ∀ ω : Ω, Xn n ω = 0 ∨ Xn n ω = 1)
    (hMeasOne : ∀ n : ℕ, MeasurableSet {ω : Ω | Xn n ω = 1})
    (hBernoulli : BernoulliZeroOneMasses μ Xn p)
    (hIndependent :
      ProbabilityTheory.iIndepSet (fun n : ℕ => {ω : Ω | Xn n ω = 1}) μ) :
    (ConvergesInProbability μ Xn (fun _ => 0) ↔ Tendsto p atTop (nhds 0)) ∧
      (ConvergesAlmostSurely μ Xn (fun _ => 0) ↔ Summable p) := by
  have hp_nonneg : ∀ n : ℕ, 0 ≤ p n := fun n => (hp n).1
  exact
    ⟨prob_10_2_convergesInProbability_iff_tendsto_p
        μ Xn p hXn hp_nonneg hBinary hBernoulli,
      prob_10_2_convergesAlmostSurely_iff_summable_p
        μ Xn p (fun n => (hXn n).aestronglyMeasurable) hp_nonneg hBinary
          hMeasOne hBernoulli hIndependent⟩
