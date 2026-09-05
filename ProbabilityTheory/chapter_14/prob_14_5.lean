/-
TASK ID: prob_14_5
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_14.thm_14_4
import ProbabilityTheory.common_support.tv_distance_core




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set Metric
open scoped Topology ENNReal

noncomputable section



def prob_14_5_weakConvergenceOnZ
    (Pseq : ℕ → ProbabilityMeasure ℤ) (P : ProbabilityMeasure ℤ) : Prop :=
  ∀ h : BoundedContinuousFunction ℤ ℝ,
    Tendsto
      (fun n : ℕ => ∫ x, h x ∂(Pseq n : Measure ℤ))
      atTop (𝓝 (∫ x, h x ∂(P : Measure ℤ)))

 
def prob_14_5_totalVariationConvergenceOnZ
    (Pseq : ℕ → ProbabilityMeasure ℤ) (P : ProbabilityMeasure ℤ) : Prop :=
  Tendsto
    (fun n : ℕ => totalVariationDistance (Pseq n : Measure ℤ) (P : Measure ℤ))
    atTop (𝓝 (0 : ℝ))

 
def prob_14_5_singletonMass (P : ProbabilityMeasure ℤ) (k : ℤ) : ℝ :=
  (P : Measure ℤ).real ({k} : Set ℤ)

 
def prob_14_5_singletonMassConvergence
    (Pseq : ℕ → ProbabilityMeasure ℤ) (P : ProbabilityMeasure ℤ) : Prop :=
  ∀ k : ℤ,
    Tendsto (fun n : ℕ => prob_14_5_singletonMass (Pseq n) k)
      atTop (𝓝 (prob_14_5_singletonMass P k))



private def prob_14_5_singletonIndicator (k : ℤ) :
    BoundedContinuousFunction ℤ ℝ := by
  classical
  refine BoundedContinuousFunction.mkOfDiscrete
    (fun x : ℤ => ({k} : Set ℤ).indicator (fun _ : ℤ => (1 : ℝ)) x) 1 ?_
  intro x y
  simp [Set.indicator_apply]
  split <;> split <;> norm_num

 
theorem prob_14_5_singletonIndicator_integral
    (P : ProbabilityMeasure ℤ) (k : ℤ) :
    (∫ x, prob_14_5_singletonIndicator k x ∂(P : Measure ℤ)) =
      prob_14_5_singletonMass P k := by
  classical
  change
    (∫ x, ({k} : Set ℤ).indicator (fun _ : ℤ => (1 : ℝ)) x ∂(P : Measure ℤ)) =
      (P : Measure ℤ).real ({k} : Set ℤ)
  rw [integral_indicator_const (1 : ℝ) (measurableSet_singleton k)]
  simp



theorem prob_14_5_weak_to_singleton_masses
    (Pseq : ℕ → ProbabilityMeasure ℤ) (P : ProbabilityMeasure ℤ) :
    prob_14_5_weakConvergenceOnZ Pseq P →
      prob_14_5_singletonMassConvergence Pseq P := by
  intro hWeak k
  have h := hWeak (prob_14_5_singletonIndicator k)
  simpa [prob_14_5_singletonIndicator_integral] using h

 
lemma prob_14_5_summable_singletonMass (P : ProbabilityMeasure ℤ) :
    Summable (fun k : ℤ => prob_14_5_singletonMass P k) := by
  change Summable (TVCore.pmfReal ((P : Measure ℤ).toPMF))
  exact TVCore.summable_pmfReal ((P : Measure ℤ).toPMF)

 
lemma prob_14_5_tsum_singletonMass (P : ProbabilityMeasure ℤ) :
    (∑' k : ℤ, prob_14_5_singletonMass P k) = 1 := by
  simpa [prob_14_5_singletonMass, TVCore.pmfReal,
    Measure.toPMF_apply, Measure.real_def] using
    TVCore.tsum_pmfReal ((P : Measure ℤ).toPMF)



theorem prob_14_5_totalVariationDistance_eq_half_tsum_abs
    (P Q : ProbabilityMeasure ℤ) :
    totalVariationDistance (P : Measure ℤ) (Q : Measure ℤ) =
      (1 / 2 : ℝ) * ∑' k : ℤ,
        |prob_14_5_singletonMass P k - prob_14_5_singletonMass Q k| := by
  simpa [TVCore.pmfDiff, TVCore.pmfReal, prob_14_5_singletonMass,
    Measure.toPMF_apply, Measure.real_def] using
    TVCore.discrete_totalVariationDistance_eq_half_tsum_abs
      ((P : Measure ℤ).toPMF) ((Q : Measure ℤ).toPMF)

private lemma prob_14_5_abs_sub_eq_add_sub_two_min {a b : ℝ} :
    |a - b| = a + b - 2 * min a b := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have hba : b ≤ a := le_of_not_ge h
    rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

private lemma prob_14_5_summable_min (P Q : ProbabilityMeasure ℤ) :
    Summable
      (fun k : ℤ =>
        min (prob_14_5_singletonMass P k) (prob_14_5_singletonMass Q k)) := by
  refine Summable.of_nonneg_of_le
    (fun k => ?_) (fun k => ?_) (prob_14_5_summable_singletonMass Q)
  · exact le_min MeasureTheory.measureReal_nonneg MeasureTheory.measureReal_nonneg
  · exact min_le_right _ _

private lemma prob_14_5_half_tsum_abs_eq_one_sub_tsum_min
    (P Q : ProbabilityMeasure ℤ) :
    (1 / 2 : ℝ) * (∑' k : ℤ,
        |prob_14_5_singletonMass P k - prob_14_5_singletonMass Q k|) =
      (1 : ℝ) -
        (∑' k : ℤ,
          min (prob_14_5_singletonMass P k) (prob_14_5_singletonMass Q k)) := by
  have hsumP := prob_14_5_summable_singletonMass P
  have hsumQ := prob_14_5_summable_singletonMass Q
  have hsumMin := prob_14_5_summable_min P Q
  have hsumTwoMin :
      Summable
        (fun k : ℤ =>
          (2 : ℝ) *
            min (prob_14_5_singletonMass P k) (prob_14_5_singletonMass Q k)) :=
    hsumMin.mul_left 2
  have htsumAbs :
      (∑' k : ℤ,
          |prob_14_5_singletonMass P k - prob_14_5_singletonMass Q k|) =
        (∑' k : ℤ,
          ((prob_14_5_singletonMass P k + prob_14_5_singletonMass Q k) -
            (2 : ℝ) *
              min (prob_14_5_singletonMass P k) (prob_14_5_singletonMass Q k))) := by
    refine tsum_congr ?_
    intro k
    exact prob_14_5_abs_sub_eq_add_sub_two_min
  have htsumCombined :
      (∑' k : ℤ,
          ((prob_14_5_singletonMass P k + prob_14_5_singletonMass Q k) -
            (2 : ℝ) *
              min (prob_14_5_singletonMass P k) (prob_14_5_singletonMass Q k))) =
        ((∑' k : ℤ, prob_14_5_singletonMass P k) +
          (∑' k : ℤ, prob_14_5_singletonMass Q k)) -
            (2 : ℝ) *
              (∑' k : ℤ,
                min (prob_14_5_singletonMass P k) (prob_14_5_singletonMass Q k)) := by
    rw [Summable.tsum_sub (hsumP.add hsumQ) hsumTwoMin]
    rw [Summable.tsum_add hsumP hsumQ]
    rw [hsumMin.tsum_mul_left 2]
  rw [htsumAbs, htsumCombined, prob_14_5_tsum_singletonMass P,
    prob_14_5_tsum_singletonMass Q]
  ring



theorem prob_14_5_singleton_masses_to_totalVariation
    (Pseq : ℕ → ProbabilityMeasure ℤ) (P : ProbabilityMeasure ℤ) :
    prob_14_5_singletonMassConvergence Pseq P →
      prob_14_5_totalVariationConvergenceOnZ Pseq P := by
  intro hsing
  have hMinTendsto :
      Tendsto
        (fun n : ℕ =>
          ∑' k : ℤ,
            min (prob_14_5_singletonMass (Pseq n) k) (prob_14_5_singletonMass P k))
        atTop (𝓝 (∑' k : ℤ, prob_14_5_singletonMass P k)) := by
    refine tendsto_tsum_of_dominated_convergence
      (prob_14_5_summable_singletonMass P) ?_ ?_
    · intro k
      have hc :
          Tendsto (fun _ : ℕ => prob_14_5_singletonMass P k)
            atTop (𝓝 (prob_14_5_singletonMass P k)) :=
        tendsto_const_nhds
      simpa [min_self] using (hsing k).min hc
    · exact Eventually.of_forall fun n k => by
        have hmin_nonneg :
            0 ≤
              min (prob_14_5_singletonMass (Pseq n) k)
                (prob_14_5_singletonMass P k) := by
          exact le_min MeasureTheory.measureReal_nonneg MeasureTheory.measureReal_nonneg
        rw [Real.norm_eq_abs, abs_of_nonneg hmin_nonneg]
        exact min_le_right _ _
  have hMinOne :
      Tendsto
        (fun n : ℕ =>
          ∑' k : ℤ,
            min (prob_14_5_singletonMass (Pseq n) k) (prob_14_5_singletonMass P k))
        atTop (𝓝 (1 : ℝ)) := by
    simpa [prob_14_5_tsum_singletonMass P] using hMinTendsto
  unfold prob_14_5_totalVariationConvergenceOnZ
  have hOneSub :
      Tendsto
        (fun n : ℕ =>
          1 -
            (∑' k : ℤ,
              min (prob_14_5_singletonMass (Pseq n) k) (prob_14_5_singletonMass P k)))
        atTop (𝓝 (0 : ℝ)) := by
    have hconst :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    simpa using hconst.sub hMinOne
  convert hOneSub using 1
  ext n
  rw [prob_14_5_totalVariationDistance_eq_half_tsum_abs]
  exact prob_14_5_half_tsum_abs_eq_one_sub_tsum_min (Pseq n) P

 
lemma prob_14_5_measureReal_le_one
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) :
    μ.real A ≤ 1 := by
  rw [Measure.real_def]
  have hA : μ A ≤ μ Set.univ := measure_mono (subset_univ A)
  have hfin : μ Set.univ ≠ ⊤ := measure_ne_top μ Set.univ
  calc
    (μ A).toReal ≤ (μ Set.univ).toReal := ENNReal.toReal_mono hfin hA
    _ = 1 := by
      rw [measure_univ]
      norm_num



lemma prob_14_5_totalVariationDistance_event_bound
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (A : Set Ω) (hA : MeasurableSet A) :
    |P.real A - Q.real A| ≤ totalVariationDistance P Q := by
  unfold totalVariationDistance
  let S : Set ℝ :=
    {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ d = |P.real A - Q.real A|}
  have hbounded : BddAbove S := by
    refine ⟨1, ?_⟩
    intro d hd
    rcases hd with ⟨B, _hB, rfl⟩
    have hP0 : 0 ≤ P.real B := measureReal_nonneg
    have hQ0 : 0 ≤ Q.real B := measureReal_nonneg
    have hP1 : P.real B ≤ 1 := prob_14_5_measureReal_le_one P B
    have hQ1 : Q.real B ≤ 1 := prob_14_5_measureReal_le_one Q B
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have hmem : |P.real A - Q.real A| ∈ S := by
    exact ⟨A, hA, rfl⟩
  exact le_csSup hbounded hmem

lemma prob_14_5_totalVariationDistance_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    0 ≤ totalVariationDistance P Q := by
  simpa using
    prob_14_5_totalVariationDistance_event_bound P Q (∅ : Set Ω) MeasurableSet.empty

lemma prob_14_5_measure_le_add_of_totalVariationDistance_lt
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ε : ℝ} (B : Set Ω) (hB : MeasurableSet B)
    (hε : totalVariationDistance P Q < ε) :
    P B ≤ Q B + ENNReal.ofReal ε := by
  have hBound := prob_14_5_totalVariationDistance_event_bound P Q B hB
  have hReal : P.real B ≤ Q.real B + ε := by
    have hNoAbs : P.real B - Q.real B ≤ totalVariationDistance P Q :=
      (le_abs_self _).trans hBound
    linarith
  have hεnonneg : 0 ≤ ε := by
    exact (prob_14_5_totalVariationDistance_nonneg P Q).trans hε.le
  calc
    P B = ENNReal.ofReal (P.real B) := by
      rw [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top P B)]
    _ ≤ ENNReal.ofReal (Q.real B + ε) := ENNReal.ofReal_le_ofReal hReal
    _ = ENNReal.ofReal (Q.real B) + ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_add measureReal_nonneg hεnonneg]
    _ = Q B + ENNReal.ofReal ε := by
      rw [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top Q B)]



theorem prob_14_5_levyProkhorovDist_le_totalVariationDistance
    (P Q : ProbabilityMeasure ℤ) :
    levyProkhorovDist (P : Measure ℤ) (Q : Measure ℤ) ≤
      totalVariationDistance (P : Measure ℤ) (Q : Measure ℤ) := by
  apply levyProkhorovDist_le_of_forall_le
  · exact prob_14_5_totalVariationDistance_nonneg (P : Measure ℤ) (Q : Measure ℤ)
  · intro ε B hε hB
    have hεpos : 0 < ε := by
      exact lt_of_le_of_lt
        (prob_14_5_totalVariationDistance_nonneg (P : Measure ℤ) (Q : Measure ℤ)) hε
    have hPB :
        (P : Measure ℤ) B ≤ (Q : Measure ℤ) B + ENNReal.ofReal ε :=
      prob_14_5_measure_le_add_of_totalVariationDistance_lt
        (P : Measure ℤ) (Q : Measure ℤ) B hB hε
    have hQB :
        (Q : Measure ℤ) B ≤ (Q : Measure ℤ) (thickening ε B) := by
      exact measure_mono (fun x hx => self_subset_thickening hεpos B hx)
    exact hPB.trans (add_le_add hQB le_rfl)



theorem prob_14_5_totalVariation_to_weak
    (Pseq : ℕ → ProbabilityMeasure ℤ) (P : ProbabilityMeasure ℤ)
    (hTV : prob_14_5_totalVariationConvergenceOnZ Pseq P) :
    prob_14_5_weakConvergenceOnZ Pseq P := by
  have hLPdist :
      Tendsto
        (fun n : ℕ =>
          levyProkhorovDist (Pseq n : Measure ℤ) (P : Measure ℤ))
        atTop (𝓝 (0 : ℝ)) := by
    refine squeeze_zero ?_ ?_ hTV
    · intro n
      rw [levyProkhorovDist]
      exact ENNReal.toReal_nonneg
    · intro n
      exact prob_14_5_levyProkhorovDist_le_totalVariationDistance (Pseq n) P
  have hLP :
      Tendsto
        (fun n : ℕ => LevyProkhorov.ofMeasure (Pseq n))
        atTop
        (𝓝 (LevyProkhorov.ofMeasure P)) := by
    refine tendsto_iff_dist_tendsto_zero.mpr ?_
    simpa [LevyProkhorov.dist_probabilityMeasure_def] using hLPdist
  have hWeak :
      Tendsto (fun n : ℕ => Pseq n) atTop (𝓝 P) := by
    have hcont :=
      (LevyProkhorov.continuous_toMeasure_probabilityMeasure
        (Ω := ℤ)).tendsto (LevyProkhorov.ofMeasure P)
    simpa [Function.comp_def] using hcont.comp hLP
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hWeak



theorem prob_14_5_weak_to_totalVariation
    (Pseq : ℕ → ProbabilityMeasure ℤ) (P : ProbabilityMeasure ℤ)
    (hWeak : prob_14_5_weakConvergenceOnZ Pseq P) :
    prob_14_5_totalVariationConvergenceOnZ Pseq P := by
  exact prob_14_5_singleton_masses_to_totalVariation Pseq P
    (prob_14_5_weak_to_singleton_masses Pseq P hWeak)



theorem prob_14_5
    (Pseq : ℕ → ProbabilityMeasure ℤ) (P : ProbabilityMeasure ℤ) :
    prob_14_5_weakConvergenceOnZ Pseq P ↔
      prob_14_5_totalVariationConvergenceOnZ Pseq P := by
  constructor
  · exact prob_14_5_weak_to_totalVariation Pseq P
  · exact prob_14_5_totalVariation_to_weak Pseq P
