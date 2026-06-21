/-
TASK ID: prob_14_11
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.chapter14_coupon_geometric_support
import ToyApollo.Output.thm_14_8

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

noncomputable section

def prob_14_11_asymptoticMeanScale (r : ℝ) (couponTypes : ℕ) : ℝ :=
  (couponTypes : ℝ) * (-Real.log (1 - r))

def prob_14_11_asymptoticVarianceScale (r : ℝ) (couponTypes : ℕ) : ℝ :=
  (couponTypes : ℝ) * (r / (1 - r) + Real.log (1 - r))

theorem prob_14_11_asymptoticVarianceCoefficient_pos
    {r : ℝ} (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    0 < r / (1 - r) + Real.log (1 - r) := by
  have hu_pos : 0 < 1 - r := sub_pos.mpr hr_lt_one
  have hu_ne_one : (1 - r)⁻¹ ≠ 1 := by
    intro h
    have h' : 1 - r = 1 := by
      exact inv_eq_one.mp h
    linarith
  have hlog_inv_lt :
      Real.log ((1 - r)⁻¹) < (1 - r)⁻¹ - 1 :=
    Real.log_lt_sub_one_of_pos (inv_pos.mpr hu_pos) hu_ne_one
  have hstrict : 1 - (1 - r)⁻¹ < Real.log (1 - r) := by
    rw [Real.log_inv] at hlog_inv_lt
    linarith
  have hrewrite : r / (1 - r) = (1 - r)⁻¹ - 1 := by
    field_simp [ne_of_gt hu_pos]
    ring
  rw [hrewrite]
  linarith

def prob_14_11_normalizedCouponValue (r : ℝ) (couponTypes : ℕ) (x : ℝ) : ℝ :=
  (x - prob_14_11_asymptoticMeanScale r couponTypes) /
    Real.sqrt (prob_14_11_asymptoticVarianceScale r couponTypes)

def prob_14_11_TextbookNormalization
    (r : ℝ) (couponTypes : ℕ → ℕ)
    (couponCollectionLaws normalizedCouponLaws : ℕ → ProbabilityMeasure ℝ) :
    Prop :=
  ∀ n : ℕ,
    normalizedCouponLaws n =
      ProbabilityMeasure.map (couponCollectionLaws n)
        ((by
          have hmeas : Measurable (prob_14_11_normalizedCouponValue r (couponTypes n)) := by
            unfold prob_14_11_normalizedCouponValue
            fun_prop
          exact hmeas.aemeasurable) :
          AEMeasurable (prob_14_11_normalizedCouponValue r (couponTypes n))
            ((couponCollectionLaws n : ProbabilityMeasure ℝ) : Measure ℝ))

structure prob_14_11_CouponRatioTriangularArraySetup where
  r : ℝ
  r_pos : 0 < r
  r_lt_one : r < 1
  couponTypes : ℕ → ℕ
  targetDistinct : ℕ → ℕ
  targetDistinct_ge_two : ∀ n : ℕ, 2 ≤ targetDistinct n
  targetDistinct_lt_couponTypes : ∀ n : ℕ, targetDistinct n < couponTypes n
  couponTypes_tendsto_atTop :
    Tendsto (fun n : ℕ => (couponTypes n : ℝ)) atTop atTop
  ratio_tendsto :
    Tendsto
      (fun n : ℕ => (targetDistinct n : ℝ) / (couponTypes n : ℝ))
      atTop
      (𝓝 r)
  standardNormalLaw : ProbabilityMeasure ℝ

lemma prob_14_11_targetDistinct_pos
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    1 ≤ S.targetDistinct n :=
  le_trans (by norm_num) (S.targetDistinct_ge_two n)

lemma prob_14_11_targetDistinct_le_couponTypes
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    S.targetDistinct n ≤ S.couponTypes n :=
  Nat.le_of_lt (S.targetDistinct_lt_couponTypes n)

lemma prob_14_11_couponTypes_pos
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    0 < S.couponTypes n :=
  lt_of_lt_of_le (by norm_num : 0 < 2)
    (le_trans (S.targetDistinct_ge_two n)
      (Nat.le_of_lt (S.targetDistinct_lt_couponTypes n)))

theorem prob_14_11_asymptoticVarianceScale_pos
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    0 < prob_14_11_asymptoticVarianceScale S.r (S.couponTypes n) := by
  unfold prob_14_11_asymptoticVarianceScale
  exact mul_pos (by exact_mod_cast prob_14_11_couponTypes_pos S n)
    (prob_14_11_asymptoticVarianceCoefficient_pos S.r_pos S.r_lt_one)

def prob_14_11_successProbability
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (n : ℕ) (i : Fin (S.targetDistinct n)) : ℝ :=
  Prob63Support.stageSuccessProb (S.couponTypes n) i

def prob_14_11_couponProbabilitySpace
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    ProbabilityMeasure (Prob63Support.CouponStageΩ (S.targetDistinct n)) :=
  ⟨Prob63Support.couponLaw (S.couponTypes n) (S.targetDistinct n)
      (prob_14_11_targetDistinct_pos S n)
      (prob_14_11_targetDistinct_le_couponTypes S n),
    by
      haveI :
          ∀ i : Fin (S.targetDistinct n),
            IsProbabilityMeasure
              (Prob63Support.stageMeasure (S.couponTypes n) (S.targetDistinct n)
                (prob_14_11_targetDistinct_pos S n)
                (prob_14_11_targetDistinct_le_couponTypes S n) i) := by
        intro i
        simpa [Prob63Support.stageMeasure, Prob63Support.stagePMF] using
          (ProbabilityTheory.isProbabilityMeasure_geometricMeasure
            (p := Prob63Support.stageSuccessProb (S.couponTypes n) i)
            (Prob63Support.stageSuccessProb_pos
              (prob_14_11_targetDistinct_pos S n)
              (prob_14_11_targetDistinct_le_couponTypes S n) i)
            (Prob63Support.stageSuccessProb_le_one
              (prob_14_11_targetDistinct_pos S n)
              (prob_14_11_targetDistinct_le_couponTypes S n) i))
      simpa [Prob63Support.couponLaw] using
        (inferInstance :
          IsProbabilityMeasure
            (Measure.pi fun i : Fin (S.targetDistinct n) =>
              Prob63Support.stageMeasure (S.couponTypes n) (S.targetDistinct n)
                (prob_14_11_targetDistinct_pos S n)
                (prob_14_11_targetDistinct_le_couponTypes S n) i))⟩

def prob_14_11_couponCollectionLaws
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (prob_14_11_couponProbabilitySpace S n)
    ((measurable_of_countable
      (Prob63Support.couponCollectionTimeReal
        (S.couponTypes n) (S.targetDistinct n))).aemeasurable)

def prob_14_11_normalizedCouponLaws
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (prob_14_11_couponCollectionLaws S n)
    ((by
      have hmeas : Measurable
          (prob_14_11_normalizedCouponValue S.r (S.couponTypes n)) := by
        unfold prob_14_11_normalizedCouponValue
        fun_prop
      exact hmeas.aemeasurable) :
      AEMeasurable (prob_14_11_normalizedCouponValue S.r (S.couponTypes n))
        ((prob_14_11_couponCollectionLaws S n : ProbabilityMeasure ℝ) : Measure ℝ))

theorem prob_14_11_textbook_normalization
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    prob_14_11_TextbookNormalization S.r S.couponTypes
      (prob_14_11_couponCollectionLaws S)
      (prob_14_11_normalizedCouponLaws S) := by
  intro n
  rfl

def prob_14_11_centeredCouponStageLaw
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (n : ℕ) (i : Fin (S.targetDistinct n)) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    ⟨Prob63Support.stageMeasure (S.couponTypes n) (S.targetDistinct n)
        (prob_14_11_targetDistinct_pos S n)
        (prob_14_11_targetDistinct_le_couponTypes S n) i,
      by
        simpa [Prob63Support.stageMeasure, Prob63Support.stagePMF] using
          (ProbabilityTheory.isProbabilityMeasure_geometricMeasure
            (p := Prob63Support.stageSuccessProb (S.couponTypes n) i)
            (Prob63Support.stageSuccessProb_pos
              (prob_14_11_targetDistinct_pos S n)
              (prob_14_11_targetDistinct_le_couponTypes S n) i)
            (Prob63Support.stageSuccessProb_le_one
              (prob_14_11_targetDistinct_pos S n)
              (prob_14_11_targetDistinct_le_couponTypes S n) i))⟩
    ((measurable_of_countable
      (fun m : ℕ =>
        Prob63Support.scalarStageWait m -
          chapter14_geometricMean (prob_14_11_successProbability S n i))).aemeasurable)

def prob_14_11_source_rows_are_independent
    (S : prob_14_11_CouponRatioTriangularArraySetup) : Prop :=
  ∀ n : ℕ,
    iIndepFun
      (fun i : Fin (S.targetDistinct n) =>
        fun ω : Prob63Support.CouponStageΩ (S.targetDistinct n) =>
          Prob63Support.scalarStageWait (ω i) -
            chapter14_geometricMean (prob_14_11_successProbability S n i))
      ((prob_14_11_couponProbabilitySpace S n : ProbabilityMeasure
        (Prob63Support.CouponStageΩ (S.targetDistinct n))) : Measure
          (Prob63Support.CouponStageΩ (S.targetDistinct n)))

theorem prob_14_11_source_rows_are_independent_proof
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    prob_14_11_source_rows_are_independent S := by
  intro n
  change iIndepFun
      (fun i : Fin (S.targetDistinct n) =>
        fun ω : Prob63Support.CouponStageΩ (S.targetDistinct n) =>
          Prob63Support.scalarStageWait (ω i) -
            chapter14_geometricMean
              (Prob63Support.stageSuccessProb (S.couponTypes n) i))
      (Prob63Support.couponLaw (S.couponTypes n) (S.targetDistinct n)
        (prob_14_11_targetDistinct_pos S n)
        (prob_14_11_targetDistinct_le_couponTypes S n))
  unfold Prob63Support.couponLaw
  haveI :
      ∀ i : Fin (S.targetDistinct n),
        IsProbabilityMeasure
          (Prob63Support.stageMeasure (S.couponTypes n) (S.targetDistinct n)
            (prob_14_11_targetDistinct_pos S n)
            (prob_14_11_targetDistinct_le_couponTypes S n) i) := by
    intro i
    simpa [Prob63Support.stageMeasure, Prob63Support.stagePMF] using
      (ProbabilityTheory.isProbabilityMeasure_geometricMeasure
        (p := Prob63Support.stageSuccessProb (S.couponTypes n) i)
        (Prob63Support.stageSuccessProb_pos
          (prob_14_11_targetDistinct_pos S n)
          (prob_14_11_targetDistinct_le_couponTypes S n) i)
        (Prob63Support.stageSuccessProb_le_one
          (prob_14_11_targetDistinct_pos S n)
          (prob_14_11_targetDistinct_le_couponTypes S n) i))
  simpa [prob_14_11_successProbability, Function.comp_def] using
    (ProbabilityTheory.iIndepFun_pi
      (μ := fun i : Fin (S.targetDistinct n) =>
        Prob63Support.stageMeasure (S.couponTypes n) (S.targetDistinct n)
          (prob_14_11_targetDistinct_pos S n)
          (prob_14_11_targetDistinct_le_couponTypes S n) i)
      (X := fun i : Fin (S.targetDistinct n) =>
        fun m : ℕ =>
          Prob63Support.scalarStageWait m -
            chapter14_geometricMean
              (Prob63Support.stageSuccessProb (S.couponTypes n) i))
      (fun i => (measurable_of_countable
        (fun m : ℕ =>
          Prob63Support.scalarStageWait m -
            chapter14_geometricMean
              (Prob63Support.stageSuccessProb (S.couponTypes n) i))).aemeasurable))

theorem prob_14_11_centeredCouponStageLaw_mean_eq_zero
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (n : ℕ) (i : Fin (S.targetDistinct n)) :
    ∫ x, x ∂((prob_14_11_centeredCouponStageLaw S n i :
        ProbabilityMeasure ℝ) : Measure ℝ) = 0 := by
  unfold prob_14_11_centeredCouponStageLaw
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    ((measurable_of_countable
      (fun m : ℕ =>
        Prob63Support.scalarStageWait m -
          chapter14_geometricMean (prob_14_11_successProbability S n i))).aemeasurable)
    (by fun_prop)]
  have hmean :=
    Prob63Support.stageWaitIntegral_eq
      (n := S.couponTypes n) (k := S.targetDistinct n)
      (prob_14_11_targetDistinct_pos S n)
      (prob_14_11_targetDistinct_le_couponTypes S n) i
  rw [integral_sub]
  change
    (∫ a : ℕ, Prob63Support.scalarStageWait a
        ∂Prob63Support.stageMeasure (S.couponTypes n) (S.targetDistinct n)
          (prob_14_11_targetDistinct_pos S n)
          (prob_14_11_targetDistinct_le_couponTypes S n) i) -
      ∫ _a : ℕ,
        chapter14_geometricMean (prob_14_11_successProbability S n i)
        ∂Prob63Support.stageMeasure (S.couponTypes n) (S.targetDistinct n)
          (prob_14_11_targetDistinct_pos S n)
          (prob_14_11_targetDistinct_le_couponTypes S n) i = 0
  rw [hmean]
  · unfold prob_14_11_successProbability chapter14_geometricMean
      Prob63Support.stageSuccessProb
    haveI : IsProbabilityMeasure
        (Prob63Support.stageMeasure (S.couponTypes n) (S.targetDistinct n)
          (prob_14_11_targetDistinct_pos S n)
          (prob_14_11_targetDistinct_le_couponTypes S n) i) := by
      simpa [Prob63Support.stageMeasure, Prob63Support.stagePMF] using
        (ProbabilityTheory.isProbabilityMeasure_geometricMeasure
          (p := Prob63Support.stageSuccessProb (S.couponTypes n) i)
          (Prob63Support.stageSuccessProb_pos
            (prob_14_11_targetDistinct_pos S n)
            (prob_14_11_targetDistinct_le_couponTypes S n) i)
          (Prob63Support.stageSuccessProb_le_one
            (prob_14_11_targetDistinct_pos S n)
            (prob_14_11_targetDistinct_le_couponTypes S n) i))
    rw [integral_const]
    simp
  · exact Prob63Support.stageWaitIntegrable
      (prob_14_11_targetDistinct_pos S n)
      (prob_14_11_targetDistinct_le_couponTypes S n) i
  · exact integrable_const _

theorem prob_14_11_centeredCouponStageLaw_second_moment_eq
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (n : ℕ) (i : Fin (S.targetDistinct n)) :
    ∫ x, x ^ 2 ∂((prob_14_11_centeredCouponStageLaw S n i :
        ProbabilityMeasure ℝ) : Measure ℝ) =
      chapter14_geometricVariance (prob_14_11_successProbability S n i) := by
  unfold prob_14_11_centeredCouponStageLaw
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    ((measurable_of_countable
      (fun m : ℕ =>
        Prob63Support.scalarStageWait m -
          chapter14_geometricMean (prob_14_11_successProbability S n i))).aemeasurable)
    (by fun_prop)]
  simpa [prob_14_11_successProbability, chapter14_geometricMean] using
    (chapter14_couponStageMeasure_centered_second_moment_eq
      (n := S.couponTypes n) (k := S.targetDistinct n)
      (prob_14_11_targetDistinct_pos S n)
      (prob_14_11_targetDistinct_le_couponTypes S n) i)

theorem prob_14_11_centeredCouponStageLaw_lyapunovMoment_eq
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (n : ℕ) (i : Fin (S.targetDistinct n)) :
    thm_14_8_lyapunovMoment (prob_14_11_centeredCouponStageLaw S n i) 2 =
      chapter14_geometricCenteredFourthMoment
        (prob_14_11_successProbability S n i) := by
  unfold thm_14_8_lyapunovMoment prob_14_11_centeredCouponStageLaw
  rw [ProbabilityMeasure.toMeasure_map]
  simp_rw [chapter14_rpow_abs_four_eq_pow_four]
  rw [integral_map
    ((measurable_of_countable
      (fun m : ℕ =>
        Prob63Support.scalarStageWait m -
          chapter14_geometricMean (prob_14_11_successProbability S n i))).aemeasurable)
    (by fun_prop)]
  simpa [prob_14_11_successProbability, chapter14_geometricMean] using
    (chapter14_couponStageMeasure_centered_fourth_moment_eq
      (n := S.couponTypes n) (k := S.targetDistinct n)
      (prob_14_11_targetDistinct_pos S n)
      (prob_14_11_targetDistinct_le_couponTypes S n) i)

def prob_14_11_rowVariance
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (n : ℕ) (i : Fin (S.targetDistinct n)) : ℝ :=
  chapter14_geometricVariance (prob_14_11_successProbability S n i)

def prob_14_11_totalVariance
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) : ℝ :=
  ∑ i : Fin (S.targetDistinct n), prob_14_11_rowVariance S n i

def prob_14_11_exactMeanSum
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) : ℝ :=
  ∑ i : Fin (S.targetDistinct n),
    chapter14_geometricMean (prob_14_11_successProbability S n i)

def prob_14_11_centeredRowSumValue
    (S : prob_14_11_CouponRatioTriangularArraySetup)
  (n : ℕ)
  (ω : Prob63Support.CouponStageΩ (S.targetDistinct n)) : ℝ :=
  ∑ i : Fin (S.targetDistinct n),
    (Prob63Support.stageWaitReal i ω -
      chapter14_geometricMean (prob_14_11_successProbability S n i))

def prob_14_11_exactStandardizedRowSumValue
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (n : ℕ)
    (ω : Prob63Support.CouponStageΩ (S.targetDistinct n)) : ℝ :=
  prob_14_11_centeredRowSumValue S n ω /
    Real.sqrt (prob_14_11_totalVariance S n)

theorem prob_14_11_centeredRowSumValue_eq_couponCollectionTimeReal_sub_meanSum
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (n : ℕ)
    (ω : Prob63Support.CouponStageΩ (S.targetDistinct n)) :
    prob_14_11_centeredRowSumValue S n ω =
      Prob63Support.couponCollectionTimeReal
        (S.couponTypes n) (S.targetDistinct n) ω -
        prob_14_11_exactMeanSum S n := by
  simp [prob_14_11_centeredRowSumValue, prob_14_11_exactMeanSum,
    Prob63Support.couponCollectionTimeReal, Finset.sum_sub_distrib]

def prob_14_11_exactToTextbookScale
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) : ℝ :=
  Real.sqrt (prob_14_11_totalVariance S n) /
    Real.sqrt (prob_14_11_asymptoticVarianceScale S.r (S.couponTypes n))

def prob_14_11_exactToTextbookShift
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) : ℝ :=
  (prob_14_11_exactMeanSum S n -
      prob_14_11_asymptoticMeanScale S.r (S.couponTypes n)) /
    Real.sqrt (prob_14_11_asymptoticVarianceScale S.r (S.couponTypes n))

def prob_14_11_exactStandardizedRowSumLaws
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map (prob_14_11_couponProbabilitySpace S n)
    ((measurable_of_countable
      (prob_14_11_exactStandardizedRowSumValue S n)).aemeasurable)

def prob_14_11_exact_standardized_sum_law_representation
    (S : prob_14_11_CouponRatioTriangularArraySetup) : Prop :=
  ∀ n : ℕ,
    prob_14_11_exactStandardizedRowSumLaws S n =
      ProbabilityMeasure.map (prob_14_11_couponProbabilitySpace S n)
        ((measurable_of_countable
          (prob_14_11_exactStandardizedRowSumValue S n)).aemeasurable)

theorem prob_14_11_exact_standardized_sum_law_representation_proof
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    prob_14_11_exact_standardized_sum_law_representation S := by
  intro n
  rfl

def prob_14_11_source_standardized_sum_law_representation
    (S : prob_14_11_CouponRatioTriangularArraySetup) : Prop :=
  prob_14_11_TextbookNormalization S.r S.couponTypes
    (prob_14_11_couponCollectionLaws S)
    (prob_14_11_normalizedCouponLaws S)

theorem prob_14_11_source_standardized_sum_law_representation_proof
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    prob_14_11_source_standardized_sum_law_representation S :=
  prob_14_11_textbook_normalization S

theorem prob_14_11_geometricVariance_ge_index_ratio
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (n : ℕ) (i : Fin (S.targetDistinct n)) :
    ((i.1 : ℝ) / (S.couponTypes n : ℝ)) ≤
      chapter14_geometricVariance (prob_14_11_successProbability S n i) := by
  have hp_pos : 0 < prob_14_11_successProbability S n i := by
    unfold prob_14_11_successProbability
    exact Prob63Support.stageSuccessProb_pos
      (prob_14_11_targetDistinct_pos S n)
      (prob_14_11_targetDistinct_le_couponTypes S n) i
  have hp_le : prob_14_11_successProbability S n i ≤ 1 := by
    unfold prob_14_11_successProbability
    exact Prob63Support.stageSuccessProb_le_one
      (prob_14_11_targetDistinct_pos S n)
      (prob_14_11_targetDistinct_le_couponTypes S n) i
  have hi_lt : i.1 < S.couponTypes n :=
    lt_of_lt_of_le i.2 (prob_14_11_targetDistinct_le_couponTypes S n)
  have hNpos : (0 : ℝ) < (S.couponTypes n : ℕ) := by
    exact_mod_cast lt_of_lt_of_le
      (Nat.succ_le_iff.mp (prob_14_11_targetDistinct_pos S n))
      (prob_14_11_targetDistinct_le_couponTypes S n)
  have hNne : ((S.couponTypes n : ℕ) : ℝ) ≠ 0 := ne_of_gt hNpos
  have hsub_cast :
      (((S.couponTypes n - i.1 : ℕ) : ℝ) =
        ((S.couponTypes n : ℕ) : ℝ) - (i.1 : ℝ)) := by
    exact Nat.cast_sub (Nat.le_of_lt hi_lt)
  have hone_minus :
      1 - prob_14_11_successProbability S n i =
        (i.1 : ℝ) / (S.couponTypes n : ℝ) := by
    unfold prob_14_11_successProbability Prob63Support.stageSuccessProb
    rw [hsub_cast]
    field_simp [hNne]
    ring
  have hgap_nonneg : 0 ≤ 1 - prob_14_11_successProbability S n i := by
    linarith
  have hp_sq_pos : 0 < prob_14_11_successProbability S n i ^ 2 :=
    sq_pos_of_ne_zero hp_pos.ne'
  have hp_sq_le_one : prob_14_11_successProbability S n i ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (prob_14_11_successProbability S n i - 1), hp_pos, hp_le]
  have hinv_sq_ge_one : 1 ≤ 1 / prob_14_11_successProbability S n i ^ 2 := by
    rw [le_div_iff₀ hp_sq_pos]
    nlinarith
  calc
    ((i.1 : ℝ) / (S.couponTypes n : ℝ))
        = 1 - prob_14_11_successProbability S n i := hone_minus.symm
    _ ≤ (1 - prob_14_11_successProbability S n i) *
          (1 / prob_14_11_successProbability S n i ^ 2) := by
        exact le_mul_of_one_le_right hgap_nonneg hinv_sq_ge_one
    _ = chapter14_geometricVariance
          (prob_14_11_successProbability S n i) := by
        unfold chapter14_geometricVariance
        ring

theorem prob_14_11_geometricVariance_row_sum_ge_index_sum
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    (∑ i : Fin (S.targetDistinct n),
      ((i.1 : ℝ) / (S.couponTypes n : ℝ))) ≤
      prob_14_11_totalVariance S n := by
  unfold prob_14_11_totalVariance prob_14_11_rowVariance
  exact Finset.sum_le_sum
    (fun i _ => prob_14_11_geometricVariance_ge_index_ratio S n i)

theorem prob_14_11_variance_scale_eventual_lower_bound
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    ∀ᶠ n : ℕ in atTop,
      (S.r ^ 2 / 64) * (S.couponTypes n : ℝ) ≤
        prob_14_11_totalVariance S n := by
  have hratio :
      ∀ᶠ n : ℕ in atTop,
        S.r / 2 <
          (S.targetDistinct n : ℝ) / (S.couponTypes n : ℝ) :=
    S.ratio_tendsto.eventually (eventually_gt_nhds (by linarith [S.r_pos]))
  have hNlarge :
      ∀ᶠ n : ℕ in atTop,
        (64 / S.r ^ 2 : ℝ) ≤ (S.couponTypes n : ℝ) :=
    S.couponTypes_tendsto_atTop.eventually_ge_atTop (64 / S.r ^ 2)
  filter_upwards [hratio, hNlarge] with n hratio_n hNlarge_n
  refine le_trans ?_ (prob_14_11_geometricVariance_row_sum_ge_index_sum S n)
  let N : ℕ := S.couponTypes n
  let m : ℕ := S.targetDistinct n
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact lt_of_lt_of_le
      (Nat.succ_le_iff.mp (prob_14_11_targetDistinct_pos S n))
      (prob_14_11_targetDistinct_le_couponTypes S n)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hm_ratio :
      S.r / 2 < (m : ℝ) / (N : ℝ) := by simpa [m, N] using hratio_n
  have hm_lower : (S.r / 2) * (N : ℝ) ≤ (m : ℝ) := by
    exact le_of_lt ((lt_div_iff₀ hN_pos).mp hm_ratio)
  have hm_sub_lower : (S.r / 4) * (N : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by
    have hbig : (1 : ℝ) ≤ (S.r / 4) * (N : ℝ) := by
      have hNlarge' : 64 / S.r ^ 2 ≤ (N : ℝ) := by simpa [N] using hNlarge_n
      have hmul := mul_le_mul_of_nonneg_left hNlarge'
        (le_of_lt (by linarith [S.r_pos] : 0 < S.r / 4))
      have hrewrite : (S.r / 4) * (64 / S.r ^ 2) = 16 / S.r := by
        field_simp [S.r_pos.ne']
        ring
      have hone : (1 : ℝ) ≤ 16 / S.r :=
        (le_div_iff₀ S.r_pos).2 (by linarith [S.r_lt_one])
      nlinarith
    have hm_sub_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have hm_pos : 0 < m := by
        dsimp [m]
        exact Nat.succ_le_iff.mp (prob_14_11_targetDistinct_pos S n)
      exact Nat.cast_pred hm_pos
    rw [hm_sub_cast]
    nlinarith [hm_lower, hbig]
  have hsum_fin :
      (∑ i : Fin m, (i.1 : ℝ)) =
        ((m * (m - 1) / 2 : ℕ) : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range]
    rw [← Nat.cast_sum]
    exact_mod_cast Finset.sum_range_id m
  have hsum_div :
      (∑ i : Fin m, ((i.1 : ℝ) / (N : ℝ))) =
        (∑ i : Fin m, (i.1 : ℝ)) / (N : ℝ) := by
    rw [Finset.sum_div]
  have hprod_lower :
      (S.r ^ 2 * (N : ℝ) * (N : ℝ)) / 16 ≤
        ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) / 2 := by
    have hmul := mul_le_mul hm_lower hm_sub_lower
      (mul_nonneg (by linarith [S.r_pos] : 0 ≤ S.r / 4) (le_of_lt hN_pos))
      (by positivity : 0 ≤ (m : ℝ))
    nlinarith
  have hfloor_lower :
      ((m : ℝ) * ((m - 1 : ℕ) : ℝ)) / 2 - 1 ≤
        ((m * (m - 1) / 2 : ℕ) : ℝ) := by
    have hmod : m * (m - 1) < 2 * ((m * (m - 1)) / 2 + 1) := by
      omega
    have hcast :
        (m : ℝ) * ((m - 1 : ℕ) : ℝ) <
          2 * (((m * (m - 1) / 2 : ℕ) : ℝ) + 1) := by
      exact_mod_cast hmod
    nlinarith
  have hlarge_absorb :
      (1 : ℝ) ≤ (S.r ^ 2 * (N : ℝ) * (N : ℝ)) / 64 := by
    have hr_sq_pos : 0 < S.r ^ 2 := sq_pos_of_pos S.r_pos
    have hNlarge' : 64 / S.r ^ 2 ≤ (N : ℝ) := by simpa [N] using hNlarge_n
    have hmul := mul_le_mul_of_nonneg_left hNlarge' (le_of_lt hr_sq_pos)
    have hrewrite : S.r ^ 2 * (64 / S.r ^ 2) = (64 : ℝ) := by
      field_simp [S.r_pos.ne', (sq_pos_of_pos S.r_pos).ne']
    have h64 : (64 : ℝ) ≤ S.r ^ 2 * (N : ℝ) := by nlinarith
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_pos_nat
    nlinarith
  have hnat_div_lower :
      (S.r ^ 2 * (N : ℝ) * (N : ℝ)) / 64 ≤
        ((m * (m - 1) / 2 : ℕ) : ℝ) := by
    nlinarith
  have hmain :
      (S.r ^ 2 / 64) * (N : ℝ) ≤
        ((m * (m - 1) / 2 : ℕ) : ℝ) / (N : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hnat_div_lower (le_of_lt hN_pos)
    have hleft :
        ((S.r ^ 2 * (N : ℝ) * (N : ℝ)) / 64) / (N : ℝ) =
          (S.r ^ 2 / 64) * (N : ℝ) := by
      field_simp [ne_of_gt hN_pos]
    nlinarith
  simpa [N, m, hsum_div, hsum_fin] using hmain

theorem prob_14_11_totalVariance_tendsto_atTop
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    Tendsto (prob_14_11_totalVariance S) atTop atTop := by
  have hc_pos : 0 < S.r ^ 2 / 64 := by
    exact div_pos (sq_pos_of_pos S.r_pos) (by norm_num)
  have hleft :
      Tendsto (fun n : ℕ => (S.r ^ 2 / 64) * (S.couponTypes n : ℝ))
        atTop atTop :=
    S.couponTypes_tendsto_atTop.const_mul_atTop hc_pos
  exact tendsto_atTop_mono' _ (prob_14_11_variance_scale_eventual_lower_bound S) hleft

theorem prob_14_11_totalVariance_pos
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    0 < prob_14_11_totalVariance S n := by
  have hN_pos : (0 : ℝ) < (S.couponTypes n : ℕ) := by
    exact_mod_cast lt_of_lt_of_le
      (Nat.succ_le_iff.mp (prob_14_11_targetDistinct_pos S n))
      (prob_14_11_targetDistinct_le_couponTypes S n)
  let i : Fin (S.targetDistinct n) := ⟨1, by
    have htwo : 2 ≤ S.targetDistinct n := S.targetDistinct_ge_two n
    omega⟩
  have hterm_pos :
      0 < ((i.1 : ℝ) / (S.couponTypes n : ℝ)) := by
    dsimp [i]
    positivity
  have hsum_pos :
      0 < ∑ j : Fin (S.targetDistinct n), ((j.1 : ℝ) / (S.couponTypes n : ℝ)) := by
    have hnonneg :
        ∀ j : Fin (S.targetDistinct n), 0 ≤ (j.1 : ℝ) / (S.couponTypes n : ℝ) := by
      intro j
      exact div_nonneg (by positivity) (le_of_lt hN_pos)
    have hle :
        ((i.1 : ℝ) / (S.couponTypes n : ℝ)) ≤
          ∑ j : Fin (S.targetDistinct n), ((j.1 : ℝ) / (S.couponTypes n : ℝ)) :=
      Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    exact lt_of_lt_of_le hterm_pos hle
  exact lt_of_lt_of_le hsum_pos
    (prob_14_11_geometricVariance_row_sum_ge_index_sum S n)

theorem prob_14_11_textbookNormalizedValue_eq_affine_exactStandardizedValue
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (n : ℕ)
    (ω : Prob63Support.CouponStageΩ (S.targetDistinct n)) :
    prob_14_11_normalizedCouponValue S.r (S.couponTypes n)
        (Prob63Support.couponCollectionTimeReal
          (S.couponTypes n) (S.targetDistinct n) ω) =
      prob_14_11_exactToTextbookScale S n *
          prob_14_11_exactStandardizedRowSumValue S n ω +
        prob_14_11_exactToTextbookShift S n := by
  have hsn_ne :
      Real.sqrt (prob_14_11_totalVariance S n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (prob_14_11_totalVariance_pos S n))
  rw [prob_14_11_exactStandardizedRowSumValue]
  rw [prob_14_11_centeredRowSumValue_eq_couponCollectionTimeReal_sub_meanSum]
  unfold prob_14_11_normalizedCouponValue prob_14_11_exactToTextbookScale
    prob_14_11_exactToTextbookShift
  field_simp [hsn_ne]
  ring

theorem prob_14_11_normalizedCouponLaws_eq_affine_exactStandardizedRowSumLaws
    (S : prob_14_11_CouponRatioTriangularArraySetup) (n : ℕ) :
    prob_14_11_normalizedCouponLaws S n =
      ProbabilityMeasure.map (prob_14_11_exactStandardizedRowSumLaws S n)
        ((by
          have hmeas : Measurable
              (fun x : ℝ =>
                prob_14_11_exactToTextbookScale S n * x +
                  prob_14_11_exactToTextbookShift S n) := by
            fun_prop
          exact hmeas.aemeasurable) :
          AEMeasurable
            (fun x : ℝ =>
              prob_14_11_exactToTextbookScale S n * x +
                prob_14_11_exactToTextbookShift S n)
            ((prob_14_11_exactStandardizedRowSumLaws S n :
              ProbabilityMeasure ℝ) : Measure ℝ)) := by
  let μ : Measure (Prob63Support.CouponStageΩ (S.targetDistinct n)) :=
    ((prob_14_11_couponProbabilitySpace S n : ProbabilityMeasure
      (Prob63Support.CouponStageΩ (S.targetDistinct n))) : Measure _)
  let T : Prob63Support.CouponStageΩ (S.targetDistinct n) → ℝ :=
    Prob63Support.couponCollectionTimeReal
      (S.couponTypes n) (S.targetDistinct n)
  let Z : Prob63Support.CouponStageΩ (S.targetDistinct n) → ℝ :=
    prob_14_11_exactStandardizedRowSumValue S n
  let f : ℝ → ℝ :=
    prob_14_11_normalizedCouponValue S.r (S.couponTypes n)
  let g : ℝ → ℝ :=
    fun x : ℝ =>
      prob_14_11_exactToTextbookScale S n * x +
        prob_14_11_exactToTextbookShift S n
  have hT : Measurable T := by
    unfold T
    exact measurable_of_countable _
  have hZ : Measurable Z := by
    unfold Z
    exact measurable_of_countable _
  have hf : Measurable f := by
    unfold f prob_14_11_normalizedCouponValue
    fun_prop
  have hg : Measurable g := by
    unfold g
    fun_prop
  have hpoint : f ∘ T =ᵐ[μ] g ∘ Z := by
    filter_upwards with ω
    exact prob_14_11_textbookNormalizedValue_eq_affine_exactStandardizedValue S n ω
  unfold prob_14_11_normalizedCouponLaws prob_14_11_couponCollectionLaws
    prob_14_11_exactStandardizedRowSumLaws
  apply Subtype.ext
  change (Measure.map f (Measure.map T μ) = Measure.map g (Measure.map Z μ))
  rw [Measure.map_map hf hT, Measure.map_map hg hZ]
  exact Measure.map_congr hpoint

def prob_14_11_arrayNotation
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    thm_14_8_TriangularArrayNotation where
  rowLength := S.targetDistinct
  rowLength_pos := fun n => Nat.succ_le_iff.mp (prob_14_11_targetDistinct_pos S n)
  variance := prob_14_11_rowVariance S
  totalVariance := prob_14_11_totalVariance S
  totalVariance_eq := by
    intro n
    rfl
  totalVariance_tendsto_atTop := prob_14_11_totalVariance_tendsto_atTop S

def prob_14_11_theoremSetup
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    thm_14_8_TriangularArraySetup where
  arrayNotation := prob_14_11_arrayNotation S
  rowLaws := prob_14_11_centeredCouponStageLaw S
  standardizedSumLaws := prob_14_11_exactStandardizedRowSumLaws S
  standardNormalLaw := S.standardNormalLaw
  sn := fun n => Real.sqrt (prob_14_11_totalVariance S n)
  sn_pos := fun n => Real.sqrt_pos.2 (prob_14_11_totalVariance_pos S n)
  sn_sq_eq_totalVariance := by
    intro n
    exact Real.sq_sqrt (le_of_lt (prob_14_11_totalVariance_pos S n))
  sn_tendsto_atTop :=
    Real.tendsto_sqrt_atTop.comp (prob_14_11_totalVariance_tendsto_atTop S)
  row_mean_zero := by
    intro n i
    exact prob_14_11_centeredCouponStageLaw_mean_eq_zero S n i
  row_variance_eq_second_moment := by
    intro n i
    exact (prob_14_11_centeredCouponStageLaw_second_moment_eq S n i).symm
  source_row_independence_on_common_probability_space :=
    prob_14_11_source_rows_are_independent S
  source_standardized_sum_law_representation :=
    prob_14_11_exact_standardized_sum_law_representation S

def prob_14_11_theoremSetupExact
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    thm_14_8_TriangularArraySetup where
  arrayNotation := prob_14_11_arrayNotation S
  rowLaws := prob_14_11_centeredCouponStageLaw S
  standardizedSumLaws := prob_14_11_exactStandardizedRowSumLaws S
  standardNormalLaw := S.standardNormalLaw
  sn := fun n => Real.sqrt (prob_14_11_totalVariance S n)
  sn_pos := fun n => Real.sqrt_pos.2 (prob_14_11_totalVariance_pos S n)
  sn_sq_eq_totalVariance := by
    intro n
    exact Real.sq_sqrt (le_of_lt (prob_14_11_totalVariance_pos S n))
  sn_tendsto_atTop :=
    Real.tendsto_sqrt_atTop.comp (prob_14_11_totalVariance_tendsto_atTop S)
  row_mean_zero := by
    intro n i
    exact prob_14_11_centeredCouponStageLaw_mean_eq_zero S n i
  row_variance_eq_second_moment := by
    intro n i
    exact (prob_14_11_centeredCouponStageLaw_second_moment_eq S n i).symm
  source_row_independence_on_common_probability_space :=
    prob_14_11_source_rows_are_independent S
  source_standardized_sum_law_representation :=
    prob_14_11_exact_standardized_sum_law_representation S

theorem prob_14_11_row_lyapunov_sum_eq_coupon_fourth_sum
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    ∀ n : ℕ,
      (∑ i : Fin ((prob_14_11_theoremSetup S).arrayNotation.rowLength n),
        thm_14_8_lyapunovMoment ((prob_14_11_theoremSetup S).rowLaws n i) 2) =
        ∑ i : Fin (S.targetDistinct n),
          chapter14_geometricCenteredFourthMoment
            (prob_14_11_successProbability S n i) := by
  intro n
  simp only [prob_14_11_theoremSetup, prob_14_11_arrayNotation]
  exact Finset.sum_congr rfl
    (fun i _hi => prob_14_11_centeredCouponStageLaw_lyapunovMoment_eq S n i)

theorem prob_14_11_totalVariance_eq_geometricVariance_sum
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    ∀ n : ℕ,
      (prob_14_11_theoremSetup S).arrayNotation.totalVariance n =
        ∑ i : Fin (S.targetDistinct n),
          chapter14_geometricVariance
            (prob_14_11_successProbability S n i) := by
  intro n
  rfl

theorem prob_14_11_centeredFourthMoment_bound_of_compact
    {a p : ℝ} (ha : 0 < a) (hap : a ≤ p) (hp_upper : p ≤ 1) :
    chapter14_geometricCenteredFourthMoment p ≤ 10 / a ^ 4 := by
  have hp_pos : 0 < p := lt_of_lt_of_le ha hap
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_four_pos : 0 < p ^ 4 := pow_pos hp_pos 4
  have ha_four_pos : 0 < a ^ 4 := pow_pos ha 4
  have hpow_le : a ^ 4 ≤ p ^ 4 := by
    gcongr
  have hinv_le : (1 / p ^ 4 : ℝ) ≤ 1 / a ^ 4 :=
    one_div_le_one_div_of_le ha_four_pos hpow_le
  have hinv_nonneg : 0 ≤ (1 / p ^ 4 : ℝ) := by positivity
  have hinv_upper_nonneg : 0 ≤ (1 / a ^ 4 : ℝ) := by positivity
  have hgap_nonneg : 0 ≤ 1 - p := by linarith
  have hgap_le : 1 - p ≤ 1 := by linarith
  have hquad_nonneg : 0 ≤ p ^ 2 - 9 * p + 9 := by
    nlinarith [sq_nonneg (p - 1), hp_nonneg, hp_upper]
  have hquad_le : p ^ 2 - 9 * p + 9 ≤ 10 := by
    have hp_sq_le_one : p ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (p - 1), hp_nonneg, hp_upper]
    nlinarith [hp_sq_le_one, hp_nonneg]
  have hfirst :
      (1 / p ^ 4 : ℝ) * (1 - p) ≤ (1 / a ^ 4) * 1 :=
    mul_le_mul hinv_le hgap_le hgap_nonneg hinv_upper_nonneg
  have hfirst_upper_nonneg : 0 ≤ (1 / a ^ 4 : ℝ) * 1 := by positivity
  have hprod :
      ((1 / p ^ 4 : ℝ) * (1 - p)) * (p ^ 2 - 9 * p + 9) ≤
        ((1 / a ^ 4) * 1) * 10 :=
    mul_le_mul hfirst hquad_le hquad_nonneg hfirst_upper_nonneg
  unfold chapter14_geometricCenteredFourthMoment
  calc
    (1 / p ^ 4 * (1 - p)) * (p ^ 2 - 9 * p + 9)
        ≤ ((1 / a ^ 4) * 1) * 10 := hprod
    _ = 10 / a ^ 4 := by ring

theorem prob_14_11_successProbability_eventually_compact
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    ∀ᶠ n : ℕ in atTop,
      ∀ i : Fin (S.targetDistinct n),
        (1 - S.r) / 2 ≤ prob_14_11_successProbability S n i ∧
          prob_14_11_successProbability S n i ≤ 1 := by
  have hlim :
      ∀ᶠ n : ℕ in atTop,
        (S.targetDistinct n : ℝ) / (S.couponTypes n : ℝ) <
          (1 + S.r) / 2 :=
    S.ratio_tendsto.eventually (eventually_lt_nhds (by linarith [S.r_lt_one]))
  filter_upwards [hlim] with n hn i
  have hN_pos_nat : 0 < S.couponTypes n := by
    have htwo : 2 ≤ S.targetDistinct n := S.targetDistinct_ge_two n
    have hlt : S.targetDistinct n < S.couponTypes n := S.targetDistinct_lt_couponTypes n
    omega
  have hN_pos : (0 : ℝ) < (S.couponTypes n : ℕ) := by exact_mod_cast hN_pos_nat
  have hN_ne : ((S.couponTypes n : ℕ) : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hi_le_target : (i.1 : ℝ) ≤ (S.targetDistinct n : ℝ) := by
    exact_mod_cast Nat.le_of_lt i.2
  have hi_ratio_le :
      (i.1 : ℝ) / (S.couponTypes n : ℝ) ≤
        (S.targetDistinct n : ℝ) / (S.couponTypes n : ℝ) := by
    exact div_le_div_of_nonneg_right hi_le_target (le_of_lt hN_pos)
  constructor
  · unfold prob_14_11_successProbability Prob63Support.stageSuccessProb
    have hi_lt_coupon : i.1 < S.couponTypes n :=
      lt_of_lt_of_le i.2 (Nat.le_of_lt (S.targetDistinct_lt_couponTypes n))
    have hsub_cast :
        (((S.couponTypes n - i.1 : ℕ) : ℝ) =
          ((S.couponTypes n : ℕ) : ℝ) - (i.1 : ℝ)) := by
      exact Nat.cast_sub (Nat.le_of_lt hi_lt_coupon)
    have hi_ratio_lt :
        (i.1 : ℝ) / (S.couponTypes n : ℝ) < (1 + S.r) / 2 :=
      lt_of_le_of_lt hi_ratio_le hn
    calc
      (1 - S.r) / 2 ≤
          1 - (i.1 : ℝ) / (S.couponTypes n : ℝ) := by
            linarith
      _ = ((S.couponTypes n - i.1 : ℕ) : ℝ) /
          (S.couponTypes n : ℝ) := by
            rw [hsub_cast]
            field_simp [hN_ne]
  · unfold prob_14_11_successProbability
    exact Prob63Support.stageSuccessProb_le_one
      (prob_14_11_targetDistinct_pos S n)
      (prob_14_11_targetDistinct_le_couponTypes S n) i

theorem prob_14_11_fourth_moment_row_sum_is_O_couponTypes
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    ∀ᶠ n : ℕ in atTop,
      (∑ i : Fin (S.targetDistinct n),
        chapter14_geometricCenteredFourthMoment
          (prob_14_11_successProbability S n i)) ≤
        (10 / (((1 - S.r) / 2) ^ 4)) * (S.couponTypes n : ℝ) := by
  have ha_pos : 0 < (1 - S.r) / 2 := by linarith [S.r_lt_one]
  filter_upwards [prob_14_11_successProbability_eventually_compact S] with n hcompact
  calc
    (∑ i : Fin (S.targetDistinct n),
      chapter14_geometricCenteredFourthMoment
        (prob_14_11_successProbability S n i))
        ≤ ∑ _i : Fin (S.targetDistinct n),
            (10 / (((1 - S.r) / 2) ^ 4) : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact prob_14_11_centeredFourthMoment_bound_of_compact ha_pos
            (hcompact i).1 (hcompact i).2
    _ = (S.targetDistinct n : ℝ) *
          (10 / (((1 - S.r) / 2) ^ 4) : ℝ) := by simp
    _ ≤ (S.couponTypes n : ℝ) *
          (10 / (((1 - S.r) / 2) ^ 4) : ℝ) := by
      have hle : (S.targetDistinct n : ℝ) ≤ (S.couponTypes n : ℝ) := by
        exact_mod_cast prob_14_11_targetDistinct_le_couponTypes S n
      exact mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (10 / (((1 - S.r) / 2) ^ 4)) * (S.couponTypes n : ℝ) := by ring

theorem prob_14_11_generalized_lyapunov_condition
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    thm_14_8_LyapunovCondition (prob_14_11_theoremSetup S) := by
  refine ⟨2, by norm_num, ?_⟩
  let T := prob_14_11_theoremSetup S
  let q : ℕ → ℝ := fun n =>
    (∑ i : Fin (T.arrayNotation.rowLength n),
      thm_14_8_lyapunovMoment (T.rowLaws n i) 2) /
        Real.rpow (T.sn n) (2 + (2 : ℝ))
  let K : ℝ := 10 / (((1 - S.r) / 2) ^ 4)
  let c : ℝ := S.r ^ 2 / 64
  let b : ℕ → ℝ := fun n => K / (c ^ 2) / (S.couponTypes n : ℝ)
  change Tendsto q atTop (𝓝 (0 : ℝ))
  refine squeeze_zero' (f := q) (g := b) ?_ ?_ ?_
  · filter_upwards with n
    have hnum_nonneg :
        0 ≤
          ∑ i : Fin (T.arrayNotation.rowLength n),
            thm_14_8_lyapunovMoment (T.rowLaws n i) 2 := by
      refine Finset.sum_nonneg ?_
      intro i _hi
      unfold thm_14_8_lyapunovMoment
      exact integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _
    have hden_nonneg :
        0 ≤ Real.rpow (T.sn n) (2 + (2 : ℝ)) :=
      Real.rpow_nonneg (le_of_lt (T.sn_pos n)) _
    exact div_nonneg hnum_nonneg hden_nonneg
  · have hc_pos : 0 < c := by
      dsimp [c]
      exact div_pos (sq_pos_of_pos S.r_pos) (by norm_num)
    filter_upwards
      [prob_14_11_fourth_moment_row_sum_is_O_couponTypes S,
        prob_14_11_variance_scale_eventual_lower_bound S]
      with n hnum_row hvar
    have hnum_bound :
        (∑ i : Fin (T.arrayNotation.rowLength n),
          thm_14_8_lyapunovMoment (T.rowLaws n i) 2) ≤
          K * (S.couponTypes n : ℝ) := by
      rw [show
        (∑ i : Fin (T.arrayNotation.rowLength n),
          thm_14_8_lyapunovMoment (T.rowLaws n i) 2) =
        ∑ i : Fin (S.targetDistinct n),
          chapter14_geometricCenteredFourthMoment
            (prob_14_11_successProbability S n i) by
          simpa [T] using prob_14_11_row_lyapunov_sum_eq_coupon_fourth_sum S n]
      simpa [K] using hnum_row
    have hsn_sq_lower :
        c * (S.couponTypes n : ℝ) ≤ T.sn n ^ 2 := by
      have hsn : T.sn n ^ 2 = prob_14_11_totalVariance S n := by
        simpa [T, prob_14_11_theoremSetup, prob_14_11_arrayNotation] using
          T.sn_sq_eq_totalVariance n
      rw [hsn]
      simpa [c] using hvar
    have hsn_pos : 0 < T.sn n := T.sn_pos n
    have hden_eq :
        Real.rpow (T.sn n) (2 + (2 : ℝ)) =
          T.sn n ^ 4 := by
      norm_num
    have hN_pos : 0 < (S.couponTypes n : ℝ) := by
      exact_mod_cast lt_of_lt_of_le
        (Nat.succ_le_iff.mp (prob_14_11_targetDistinct_pos S n))
        (prob_14_11_targetDistinct_le_couponTypes S n)
    have hden_lower :
        (c * (S.couponTypes n : ℝ)) ^ 2 ≤
          Real.rpow (T.sn n) (2 + (2 : ℝ)) := by
      rw [hden_eq]
      have hsquare :
          (c * (S.couponTypes n : ℝ)) ^ 2 ≤
            (T.sn n ^ 2) ^ 2 := by
        have hleft_nonneg : 0 ≤ c * (S.couponTypes n : ℝ) :=
          le_of_lt (mul_pos hc_pos hN_pos)
        have hright_nonneg : 0 ≤ T.sn n ^ 2 := sq_nonneg _
        nlinarith [sq_nonneg
          (T.sn n ^ 2 - c * (S.couponTypes n : ℝ)),
          hsn_sq_lower, hleft_nonneg, hright_nonneg]
      nlinarith
    have hquot_bound :
        (∑ i : Fin (T.arrayNotation.rowLength n),
          thm_14_8_lyapunovMoment (T.rowLaws n i) 2) /
            Real.rpow (T.sn n) (2 + (2 : ℝ)) ≤
          (K * (S.couponTypes n : ℝ)) /
            ((c * (S.couponTypes n : ℝ)) ^ 2) := by
      gcongr
    have hsimplify :
        (K * (S.couponTypes n : ℝ)) /
            ((c * (S.couponTypes n : ℝ)) ^ 2) =
          K / (c ^ 2) / (S.couponTypes n : ℝ) := by
      field_simp [ne_of_gt hN_pos, ne_of_gt hc_pos]
    simpa [q, b, hsimplify] using hquot_bound
  · have hb :
        Tendsto (fun n : ℕ => K / (c ^ 2) / (S.couponTypes n : ℝ))
          atTop (𝓝 (0 : ℝ)) := by
      have hconst :
          Tendsto (fun x : ℝ => K / (c ^ 2) / x) atTop (𝓝 (0 : ℝ)) := by
        exact tendsto_const_nhds.div_atTop tendsto_id
      exact hconst.comp S.couponTypes_tendsto_atTop
    simpa [b] using hb

theorem prob_14_11_generalized_lyapunov_condition_exact
    (S : prob_14_11_CouponRatioTriangularArraySetup) :
    thm_14_8_LyapunovCondition (prob_14_11_theoremSetupExact S) := by
  simpa [prob_14_11_theoremSetupExact, prob_14_11_theoremSetup] using
    prob_14_11_generalized_lyapunov_condition S

theorem prob_14_11_exact_standardized_clt
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook (prob_14_11_theoremSetupExact S)) :
    Tendsto (prob_14_11_exactStandardizedRowSumLaws S) atTop
      (𝓝 S.standardNormalLaw) := by
  have hCLT :
      thm_14_8_conclusion (prob_14_11_theoremSetupExact S) :=
    thm_14_8 (prob_14_11_theoremSetupExact S) H
      (Or.inr (prob_14_11_generalized_lyapunov_condition_exact S))
  simpa [thm_14_8_conclusion, prob_14_11_theoremSetupExact] using hCLT

theorem prob_14_11_asymptoticNormality
    (S : prob_14_11_CouponRatioTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook (prob_14_11_theoremSetupExact S)) :
    Tendsto (prob_14_11_exactStandardizedRowSumLaws S) atTop
      (𝓝 S.standardNormalLaw) :=
  prob_14_11_exact_standardized_clt S H

def prob_14_11_ExactStandardizedConvergence
    (S : prob_14_11_CouponRatioTriangularArraySetup) : Prop :=
  prob_14_11_exact_standardized_sum_law_representation S ∧
    Tendsto (prob_14_11_exactStandardizedRowSumLaws S) atTop
      (𝓝 S.standardNormalLaw)
