/-
TASK ID: prob_10_6
TYPE: Problem
SOURCE PLAN: chapter10-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.tv_distance_core

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

noncomputable section

def SingletonMassesConverge {Ω : Type*} [MeasurableSpace Ω]
    (μn : ℕ → Measure Ω) (μ : Measure Ω) : Prop :=
  ∀ x : Ω, Tendsto (fun n : ℕ => (μn n).real {x}) atTop (nhds (μ.real {x}))

def CountableSampleBoundedTestFunction {Ω : Type*} (f : Ω → ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : Ω, |f x| ≤ C

noncomputable def CountableSampleMeasuresConvergeInDistribution {Ω : Type*}
    [MeasurableSpace Ω] (μn : ℕ → Measure Ω) (μ : Measure Ω) : Prop :=
  ∀ f : Ω → ℝ, Measurable f → CountableSampleBoundedTestFunction f →
    Tendsto (fun n : ℕ => ∫ x, f x ∂ μn n) atTop (nhds (∫ x, f x ∂ μ))

theorem prob_10_6_singleton_masses_of_countableSampleDistribution {Ω : Type*}
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μn : ℕ → Measure Ω) (μ : Measure Ω)
    (hWeak : CountableSampleMeasuresConvergeInDistribution μn μ) :
    SingletonMassesConverge μn μ := by
  intro x
  let f : Ω → ℝ := ({x} : Set Ω).indicator (fun _ : Ω => (1 : ℝ))
  have hf : Measurable f := by
    exact (measurable_const : Measurable fun _ : Ω => (1 : ℝ)).indicator
      (measurableSet_singleton x)
  have hb : CountableSampleBoundedTestFunction f := by
    refine ⟨1, ?_⟩
    intro y
    by_cases hy : y = x
    · simp [f, hy]
    · simp [f, hy]
  have htest := hWeak f hf hb
  simpa [SingletonMassesConverge, f, integral_indicator_one] using htest

private lemma prob_10_6_summable_singletonMass {Ω : Type*} [MeasurableSpace Ω]
    [Countable Ω] [MeasurableSingletonClass Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] :
    Summable (fun x : Ω => ν.real ({x} : Set Ω)) := by
  change Summable (TVCore.pmfReal ν.toPMF)
  exact TVCore.summable_pmfReal ν.toPMF

private lemma prob_10_6_tsum_singletonMass {Ω : Type*} [MeasurableSpace Ω]
    [Countable Ω] [MeasurableSingletonClass Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] :
    (∑' x : Ω, ν.real ({x} : Set Ω)) = 1 := by
  simpa [TVCore.pmfReal, Measure.toPMF_apply, Measure.real_def] using
    TVCore.tsum_pmfReal (ν.toPMF)

private lemma prob_10_6_integral_eq_tsum_singletonMass {Ω : Type*}
    [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ)
    (hf_int : Integrable f ν) :
    (∫ x, f x ∂ν) = ∑' x : Ω, f x * ν.real ({x} : Set Ω) := by
  calc
    (∫ x, f x ∂ν) = ∫ x, f x ∂(ν.toPMF.toMeasure) := by
      rw [Measure.toPMF_toMeasure]
    _ = ∑' x : Ω, (ν.toPMF x).toReal • f x := by
      exact PMF.integral_eq_tsum ν.toPMF f (by simpa [Measure.toPMF_toMeasure] using hf_int)
    _ = ∑' x : Ω, f x * ν.real ({x} : Set Ω) := by
      refine tsum_congr ?_
      intro x
      simp [Measure.toPMF_apply, Measure.real_def, mul_comm]

private lemma prob_10_6_abs_sub_eq_add_sub_two_min {a b : ℝ} :
    |a - b| = a + b - 2 * min a b := by
  by_cases h : a ≤ b
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have hba : b ≤ a := le_of_not_ge h
    rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

private lemma prob_10_6_summable_min_singletonMass {Ω : Type*} [MeasurableSpace Ω]
    [Countable Ω] [MeasurableSingletonClass Ω] (ν ξ : Measure Ω)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Summable
      (fun x : Ω =>
        min (ν.real ({x} : Set Ω)) (ξ.real ({x} : Set Ω))) := by
  refine Summable.of_nonneg_of_le
    (fun x => ?_) (fun x => ?_) (prob_10_6_summable_singletonMass ξ)
  · exact le_min MeasureTheory.measureReal_nonneg MeasureTheory.measureReal_nonneg
  · exact min_le_right _ _

private lemma prob_10_6_half_tsum_abs_eq_one_sub_tsum_min {Ω : Type*}
    [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (ν ξ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    (1 / 2 : ℝ) *
        (∑' x : Ω, |ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω)|) =
      (1 : ℝ) -
        (∑' x : Ω,
          min (ν.real ({x} : Set Ω)) (ξ.real ({x} : Set Ω))) := by
  have hsumν := prob_10_6_summable_singletonMass ν
  have hsumξ := prob_10_6_summable_singletonMass ξ
  have hsumMin := prob_10_6_summable_min_singletonMass ν ξ
  have hsumTwoMin :
      Summable
        (fun x : Ω =>
          (2 : ℝ) *
            min (ν.real ({x} : Set Ω)) (ξ.real ({x} : Set Ω))) :=
    hsumMin.mul_left 2
  have htsumAbs :
      (∑' x : Ω, |ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω)|) =
        (∑' x : Ω,
          ((ν.real ({x} : Set Ω) + ξ.real ({x} : Set Ω)) -
            (2 : ℝ) * min (ν.real ({x} : Set Ω)) (ξ.real ({x} : Set Ω)))) := by
    refine tsum_congr ?_
    intro x
    exact prob_10_6_abs_sub_eq_add_sub_two_min
  have htsumCombined :
      (∑' x : Ω,
          ((ν.real ({x} : Set Ω) + ξ.real ({x} : Set Ω)) -
            (2 : ℝ) * min (ν.real ({x} : Set Ω)) (ξ.real ({x} : Set Ω)))) =
        ((∑' x : Ω, ν.real ({x} : Set Ω)) +
          (∑' x : Ω, ξ.real ({x} : Set Ω))) -
            (2 : ℝ) *
              (∑' x : Ω,
                min (ν.real ({x} : Set Ω)) (ξ.real ({x} : Set Ω))) := by
    rw [Summable.tsum_sub (hsumν.add hsumξ) hsumTwoMin]
    rw [Summable.tsum_add hsumν hsumξ]
    rw [hsumMin.tsum_mul_left 2]
  rw [htsumAbs, htsumCombined, prob_10_6_tsum_singletonMass ν,
    prob_10_6_tsum_singletonMass ξ]
  ring

private lemma prob_10_6_summable_abs_singletonMass_sub {Ω : Type*}
    [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (ν ξ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Summable
      (fun x : Ω => |ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω)|) := by
  simpa [TVCore.pmfDiff, TVCore.pmfReal, Measure.toPMF_apply, Measure.real_def] using
    TVCore.summable_abs_pmfDiff (ν.toPMF) (ξ.toPMF)

private lemma prob_10_6_tendsto_tsum_abs_singletonMass_sub {Ω : Type*}
    [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (μn : ℕ → Measure Ω) (μ : Measure Ω)
    (hμn : ∀ n : ℕ, IsProbabilityMeasure (μn n)) (hμ : IsProbabilityMeasure μ)
    (hsing : SingletonMassesConverge μn μ) :
    Tendsto
      (fun n : ℕ =>
        ∑' x : Ω, |(μn n).real ({x} : Set Ω) - μ.real ({x} : Set Ω)|)
      atTop (nhds (0 : ℝ)) := by
  letI : IsProbabilityMeasure μ := hμ
  have hMinTendsto :
      Tendsto
        (fun n : ℕ =>
          ∑' x : Ω,
            min ((μn n).real ({x} : Set Ω)) (μ.real ({x} : Set Ω)))
        atTop (nhds (∑' x : Ω, μ.real ({x} : Set Ω))) := by
    refine tendsto_tsum_of_dominated_convergence
      (prob_10_6_summable_singletonMass μ) ?_ ?_
    · intro x
      have hc :
          Tendsto (fun _ : ℕ => μ.real ({x} : Set Ω))
            atTop (nhds (μ.real ({x} : Set Ω))) :=
        tendsto_const_nhds
      simpa [SingletonMassesConverge, min_self] using (hsing x).min hc
    · exact Eventually.of_forall fun n x => by
        have hmin_nonneg :
            0 ≤ min ((μn n).real ({x} : Set Ω)) (μ.real ({x} : Set Ω)) := by
          exact le_min MeasureTheory.measureReal_nonneg MeasureTheory.measureReal_nonneg
        rw [Real.norm_eq_abs, abs_of_nonneg hmin_nonneg]
        exact min_le_right _ _
  have hMinOne :
      Tendsto
        (fun n : ℕ =>
          ∑' x : Ω,
            min ((μn n).real ({x} : Set Ω)) (μ.real ({x} : Set Ω)))
        atTop (nhds (1 : ℝ)) := by
    simpa [prob_10_6_tsum_singletonMass μ] using hMinTendsto
  have hOneSub :
      Tendsto
        (fun n : ℕ =>
          1 -
            (∑' x : Ω,
              min ((μn n).real ({x} : Set Ω)) (μ.real ({x} : Set Ω))))
        atTop (nhds (0 : ℝ)) := by
    have hconst :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (1 : ℝ)) :=
      tendsto_const_nhds
    simpa using hconst.sub hMinOne
  have hHalf :
      Tendsto
        (fun n : ℕ =>
          (1 / 2 : ℝ) *
            (∑' x : Ω, |(μn n).real ({x} : Set Ω) - μ.real ({x} : Set Ω)|))
        atTop (nhds (0 : ℝ)) := by
    convert hOneSub using 1
    ext n
    letI : IsProbabilityMeasure (μn n) := hμn n
    exact prob_10_6_half_tsum_abs_eq_one_sub_tsum_min (μn n) μ
  have hScaled := hHalf.const_mul (2 : ℝ)
  simpa [mul_assoc] using hScaled

private lemma prob_10_6_integrable_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {f : Ω → ℝ}
    (hf : Measurable f) {B : ℝ} (hB : ∀ x : Ω, |f x| ≤ B) :
    Integrable f ν := by
  refine Integrable.of_bound hf.aestronglyMeasurable B ?_
  exact Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using hB x

private lemma prob_10_6_summable_mul_singletonMass {Ω : Type*}
    [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω → ℝ)
    {B : ℝ} (_hB_nonneg : 0 ≤ B) (hB : ∀ x : Ω, |f x| ≤ B) :
    Summable (fun x : Ω => f x * ν.real ({x} : Set Ω)) := by
  refine ((prob_10_6_summable_singletonMass ν).mul_left B).of_norm_bounded ?_
  intro x
  have hmass_nonneg : 0 ≤ ν.real ({x} : Set Ω) := MeasureTheory.measureReal_nonneg
  calc
    ‖f x * ν.real ({x} : Set Ω)‖
        = |f x| * ν.real ({x} : Set Ω) := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hmass_nonneg]
    _ ≤ B * ν.real ({x} : Set Ω) :=
        mul_le_mul_of_nonneg_right (hB x) hmass_nonneg

private lemma prob_10_6_integral_sub_bound {Ω : Type*}
    [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (ν ξ : Measure Ω) [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (f : Ω → ℝ) (hfν : Integrable f ν) (hfξ : Integrable f ξ)
    {B : ℝ} (hB_nonneg : 0 ≤ B) (hB : ∀ x : Ω, |f x| ≤ B) :
    |(∫ x, f x ∂ν) - (∫ x, f x ∂ξ)| ≤
      B * (∑' x : Ω, |ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω)|) := by
  have hsumν := prob_10_6_summable_mul_singletonMass ν f hB_nonneg hB
  have hsumξ := prob_10_6_summable_mul_singletonMass ξ f hB_nonneg hB
  have hsumAbs := prob_10_6_summable_abs_singletonMass_sub ν ξ
  have hsumBound :
      Summable
        (fun x : Ω =>
          B * |ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω)|) :=
    hsumAbs.mul_left B
  have hsumDiff :
      Summable
        (fun x : Ω => f x * (ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω))) := by
    simpa [mul_sub] using hsumν.sub hsumξ
  have hdiff_eq :
      (∫ x, f x ∂ν) - (∫ x, f x ∂ξ) =
        ∑' x : Ω, f x * (ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω)) := by
    rw [prob_10_6_integral_eq_tsum_singletonMass ν f hfν,
      prob_10_6_integral_eq_tsum_singletonMass ξ f hfξ]
    rw [← Summable.tsum_sub hsumν hsumξ]
    refine tsum_congr ?_
    intro x
    ring
  calc
    |(∫ x, f x ∂ν) - (∫ x, f x ∂ξ)|
        = ‖∑' x : Ω, f x * (ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω))‖ := by
            rw [hdiff_eq, Real.norm_eq_abs]
    _ ≤ ∑' x : Ω, B * |ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω)| := by
        exact HasSum.norm_le_of_bounded
          hsumDiff.hasSum
          hsumBound.hasSum
          (fun x => by
            calc
              ‖f x * (ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω))‖
                  = |f x| *
                      |ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω)| := by
                      rw [Real.norm_eq_abs, abs_mul]
              _ ≤ B * |ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω)| :=
                  mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _))
    _ = B * (∑' x : Ω, |ν.real ({x} : Set Ω) - ξ.real ({x} : Set Ω)|) := by
        rw [hsumAbs.tsum_mul_left B]

private theorem prob_10_6_singleton_masses_to_distribution_internal {Ω : Type*}
    [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
    (μn : ℕ → Measure Ω) (μ : Measure Ω)
    (hμn : ∀ n : ℕ, IsProbabilityMeasure (μn n)) (hμ : IsProbabilityMeasure μ) :
    SingletonMassesConverge μn μ → CountableSampleMeasuresConvergeInDistribution μn μ := by
  intro hsing f hf hb
  rcases hb with ⟨C, hC⟩
  let B : ℝ := max C 0
  have hB_nonneg : 0 ≤ B := le_max_right C 0
  have hB : ∀ x : Ω, |f x| ≤ B := fun x => (hC x).trans (le_max_left C 0)
  letI : IsProbabilityMeasure μ := hμ
  have hfμ : Integrable f μ := prob_10_6_integrable_of_bounded μ hf hB
  have hAbs :=
    prob_10_6_tendsto_tsum_abs_singletonMass_sub μn μ hμn hμ hsing
  have hBoundTendsto :
      Tendsto
        (fun n : ℕ =>
          B *
            (∑' x : Ω, |(μn n).real ({x} : Set Ω) - μ.real ({x} : Set Ω)|))
        atTop (nhds (0 : ℝ)) := by
    simpa using hAbs.const_mul B
  have hAbsInt :
      Tendsto
        (fun n : ℕ => |(∫ x, f x ∂(μn n)) - (∫ x, f x ∂μ)|)
        atTop (nhds (0 : ℝ)) := by
    refine squeeze_zero (fun n => abs_nonneg _) ?_ hBoundTendsto
    intro n
    letI : IsProbabilityMeasure (μn n) := hμn n
    have hfμn : Integrable f (μn n) :=
      prob_10_6_integrable_of_bounded (μn n) hf hB
    exact prob_10_6_integral_sub_bound (μn n) μ f hfμn hfμ hB_nonneg hB
  exact tendsto_iff_norm_sub_tendsto_zero.2 (by
    simpa [Real.norm_eq_abs] using hAbsInt)

theorem prob_10_6 {Ω : Type*} [MeasurableSpace Ω] [Countable Ω]
    [MeasurableSingletonClass Ω] (μn : ℕ → Measure Ω) (μ : Measure Ω)
    (hμn : ∀ n : ℕ, IsProbabilityMeasure (μn n)) (hμ : IsProbabilityMeasure μ) :
    CountableSampleMeasuresConvergeInDistribution μn μ ↔ SingletonMassesConverge μn μ := by
  exact ⟨prob_10_6_singleton_masses_of_countableSampleDistribution μn μ,
    prob_10_6_singleton_masses_to_distribution_internal μn μ hμn hμ⟩

end
