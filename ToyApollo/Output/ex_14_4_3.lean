/-
TASK ID: ex_14_4_3
TYPE: Example_Proof
SOURCE PLAN: chapter14-central-limit-theorems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.ex_14_4_3_coupon_stage_support

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section

def ex_14_4_3_couponMean (n : ℕ) : ℝ :=
  Prob63Support.couponCollectorValueReal
    (ex_14_4_3_couponTypes n) (ex_14_4_3_targetDistinct n)

def ex_14_4_3_asymptoticMeanScale (n : ℕ) : ℝ :=
  (ex_14_4_3_couponTypes n : ℝ) * Real.log 2

def ex_14_4_3_asymptoticVarianceScale (n : ℕ) : ℝ :=
  (ex_14_4_3_couponTypes n : ℝ) * (1 - Real.log 2)

def ex_14_4_3_normalizedCouponValue (n : ℕ) (x : ℝ) : ℝ :=
  (x - ex_14_4_3_asymptoticMeanScale n) /
    Real.sqrt (ex_14_4_3_asymptoticVarianceScale n)

def ex_14_4_3_TextbookNormalization
    (couponCollectionLaws normalizedCouponLaws : ℕ → ProbabilityMeasure ℝ) :
    Prop :=
  ∀ n : ℕ,
    normalizedCouponLaws n =
      ProbabilityMeasure.map (couponCollectionLaws n)
        ((by
          have hmeas : Measurable (ex_14_4_3_normalizedCouponValue n) := by
            unfold ex_14_4_3_normalizedCouponValue
            fun_prop
          exact hmeas.aemeasurable) :
          AEMeasurable (ex_14_4_3_normalizedCouponValue n)
            ((couponCollectionLaws n : ProbabilityMeasure ℝ) : Measure ℝ))

structure ex_14_4_3_CouponTriangularArraySetup where
  theoremSetup : thm_14_8_TriangularArraySetup
  couponCollectionLaws : ℕ → ProbabilityMeasure ℝ
  normalizedCouponLaws : ℕ → ProbabilityMeasure ℝ
  standardNormalLaw : ProbabilityMeasure ℝ
  row_length_matches :
    ∀ n : ℕ,
      theoremSetup.arrayNotation.rowLength n = ex_14_4_3_targetDistinct n
  row_laws_are_centered_coupon_stage_laws :
    ∀ n : ℕ, ∀ i : Fin (theoremSetup.arrayNotation.rowLength n),
      theoremSetup.rowLaws n i =
        ex_14_4_3_centeredCouponStageLaw n
          (Fin.cast (row_length_matches n) i)
  standardized_laws_eq :
    theoremSetup.standardizedSumLaws = normalizedCouponLaws
  standard_normal_eq :
    theoremSetup.standardNormalLaw = standardNormalLaw
  source_rows_are_independent :
    theoremSetup.source_row_independence_on_common_probability_space
  source_coupon_collection_law_is_stage_sum :
    theoremSetup.source_standardized_sum_law_representation
  source_normalized_law_represents_centered_T :
    theoremSetup.standardizedSumLaws = normalizedCouponLaws
  textbook_normalization :
    ex_14_4_3_TextbookNormalization couponCollectionLaws normalizedCouponLaws

theorem ex_14_4_3_row_lyapunov_sum_eq_coupon_fourth_sum
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    ∀ n : ℕ,
      (∑ i : Fin (C.theoremSetup.arrayNotation.rowLength n),
        thm_14_8_lyapunovMoment (C.theoremSetup.rowLaws n i) 2) =
        ∑ i : Fin (ex_14_4_3_targetDistinct n),
          ex_14_4_3_geometricCenteredFourthMoment
            (ex_14_4_3_successProbability n i) := by
  intro n
  let e : Fin (C.theoremSetup.arrayNotation.rowLength n) ≃
      Fin (ex_14_4_3_targetDistinct n) :=
    finCongr (C.row_length_matches n)
  refine Fintype.sum_equiv e _ _ ?_
  intro i
  simp [e, C.row_laws_are_centered_coupon_stage_laws,
    ex_14_4_3_centeredCouponStageLaw_lyapunovMoment_eq]

theorem ex_14_4_3_totalVariance_eq_geometricVariance_sum
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    ∀ n : ℕ,
      C.theoremSetup.arrayNotation.totalVariance n =
        ∑ i : Fin (ex_14_4_3_targetDistinct n),
          ex_14_4_3_geometricVariance
            (ex_14_4_3_successProbability n i) := by
  intro n
  rw [C.theoremSetup.arrayNotation.totalVariance_eq n]
  let e : Fin (C.theoremSetup.arrayNotation.rowLength n) ≃
      Fin (ex_14_4_3_targetDistinct n) :=
    finCongr (C.row_length_matches n)
  refine Fintype.sum_equiv e _ _ ?_
  intro i
  rw [C.theoremSetup.row_variance_eq_second_moment]
  simp [e, C.row_laws_are_centered_coupon_stage_laws,
    ex_14_4_3_centeredCouponStageLaw_second_moment_eq]

theorem ex_14_4_3_variance_scale_lower_bound
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    ∀ᶠ n : ℕ in atTop,
      (ex_14_4_3_couponTypes n : ℝ) / 64 ≤
        C.theoremSetup.arrayNotation.totalVariance n := by
  filter_upwards [ex_14_4_3_index_ratio_sum_linear_lower_bound] with n hindex
  rw [ex_14_4_3_totalVariance_eq_geometricVariance_sum C n]
  exact le_trans hindex (ex_14_4_3_geometricVariance_row_sum_ge_index_sum n)

structure ex_14_4_3_GeometricMomentFormulasForStage
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) : Prop where
  mgf_formula :
    ∀ t : ℝ,
      ‖(1 - ex_14_4_3_successProbability n i) * Real.exp t‖ < 1 →
        ProbabilityTheory.mgf Prob63Support.scalarStageWait
          (Prob63Support.stageMeasure (ex_14_4_3_couponTypes n)
            (ex_14_4_3_targetDistinct n)
            (ex_14_4_3_targetDistinct_pos n)
            (ex_14_4_3_targetDistinct_le_couponTypes n) i) t =
          ex_14_4_3_geometricMgf (ex_14_4_3_successProbability n i) t
  mean_formula :
    ∫ m, Prob63Support.scalarStageWait m
      ∂(Prob63Support.stageMeasure (ex_14_4_3_couponTypes n)
        (ex_14_4_3_targetDistinct n)
        (ex_14_4_3_targetDistinct_pos n)
        (ex_14_4_3_targetDistinct_le_couponTypes n) i) =
      ex_14_4_3_geometricMean (ex_14_4_3_successProbability n i)
  variance_formula :
    ∫ x, x ^ 2 ∂((ex_14_4_3_centeredCouponStageLaw n i :
      ProbabilityMeasure ℝ) : Measure ℝ) =
        ex_14_4_3_geometricVariance (ex_14_4_3_successProbability n i)
  centered_fourth_formula :
    thm_14_8_lyapunovMoment (ex_14_4_3_centeredCouponStageLaw n i) 2 =
      ex_14_4_3_geometricCenteredFourthMoment
        (ex_14_4_3_successProbability n i)

theorem ex_14_4_3_geometric_moment_formulas_verified
    (n : ℕ) (i : Fin (ex_14_4_3_targetDistinct n)) :
    ex_14_4_3_GeometricMomentFormulasForStage n i := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    simpa [ex_14_4_3_successProbability, ex_14_4_3_geometricMgf] using
      (ex_14_4_3_stageMeasure_mgf_eq
        (n := ex_14_4_3_couponTypes n)
        (k := ex_14_4_3_targetDistinct n)
        (ex_14_4_3_targetDistinct_pos n)
        (ex_14_4_3_targetDistinct_le_couponTypes n) i
        (t := t) ht)
  · have hmean :=
      Prob63Support.stageWaitIntegral_eq
        (n := ex_14_4_3_couponTypes n)
        (k := ex_14_4_3_targetDistinct n)
        (ex_14_4_3_targetDistinct_pos n)
        (ex_14_4_3_targetDistinct_le_couponTypes n) i
    rw [hmean]
    unfold ex_14_4_3_geometricMean ex_14_4_3_successProbability
      Prob63Support.stageSuccessProb
    have hN : ((ex_14_4_3_couponTypes n : ℕ) : ℝ) ≠ 0 := by
      unfold ex_14_4_3_couponTypes
      positivity
    have hi_lt :
        i.1 < ex_14_4_3_couponTypes n :=
      lt_of_lt_of_le i.2 (ex_14_4_3_targetDistinct_le_couponTypes n)
    have hsub :
        (((ex_14_4_3_couponTypes n - i.1 : ℕ) : ℝ) =
          ((ex_14_4_3_couponTypes n : ℕ) : ℝ) - (i.1 : ℝ)) := by
      exact Nat.cast_sub (Nat.le_of_lt hi_lt)
    have hsub_ne : ((ex_14_4_3_couponTypes n - i.1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt hi_lt).ne'
    rw [hsub]
    field_simp [hN, hsub_ne]
  · exact ex_14_4_3_centeredCouponStageLaw_second_moment_eq n i
  · exact ex_14_4_3_centeredCouponStageLaw_lyapunovMoment_eq n i

structure ex_14_4_3_LyapunovVerification
    (C : ex_14_4_3_CouponTriangularArraySetup) where
  moment_formulas :
    ∀ n : ℕ, ∀ i : Fin (ex_14_4_3_targetDistinct n),
      ex_14_4_3_GeometricMomentFormulasForStage n i
  fourth_moment_sum_bound :
    ∀ n : ℕ,
      (∑ i : Fin (ex_14_4_3_targetDistinct n),
        ex_14_4_3_geometricCenteredFourthMoment
          (ex_14_4_3_successProbability n i)) ≤
        160 * (ex_14_4_3_couponTypes n : ℝ)
  variance_linear_lower_bound :
    ∀ᶠ n : ℕ in atTop,
      (ex_14_4_3_couponTypes n : ℝ) / 64 ≤
        C.theoremSetup.arrayNotation.totalVariance n
  variance_asymptotic :
    Tendsto
      (fun n : ℕ =>
        C.theoremSetup.sn n ^ 2 / (ex_14_4_3_couponTypes n : ℝ))
      atTop (𝓝 (1 - Real.log 2))
  mean_asymptotic :
    Tendsto
      (fun n : ℕ =>
        ex_14_4_3_couponMean n / (ex_14_4_3_couponTypes n : ℝ))
      atTop (𝓝 (Real.log 2))

theorem ex_14_4_3_lyapunov_condition_from_fourth_moment_riemann_sum
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    thm_14_8_LyapunovCondition C.theoremSetup := by
  refine ⟨2, by norm_num, ?_⟩
  let q : ℕ → ℝ := fun n =>
    (∑ i : Fin (C.theoremSetup.arrayNotation.rowLength n),
      thm_14_8_lyapunovMoment (C.theoremSetup.rowLaws n i) 2) /
        Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ))
  let b : ℕ → ℝ := fun n =>
    (160 * 4096 : ℝ) / (ex_14_4_3_couponTypes n : ℝ)
  change Tendsto q atTop (𝓝 (0 : ℝ))
  refine squeeze_zero' (f := q) (g := b) ?_ ?_ ?_
  · filter_upwards with n
    have hnum_nonneg :
        0 ≤
          ∑ i : Fin (C.theoremSetup.arrayNotation.rowLength n),
            thm_14_8_lyapunovMoment (C.theoremSetup.rowLaws n i) 2 := by
      refine Finset.sum_nonneg ?_
      intro i _hi
      unfold thm_14_8_lyapunovMoment
      exact integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg x) _
    have hden_nonneg :
        0 ≤ Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ)) := by
      exact Real.rpow_nonneg (le_of_lt (C.theoremSetup.sn_pos n)) _
    exact div_nonneg hnum_nonneg hden_nonneg
  · filter_upwards [ex_14_4_3_variance_scale_lower_bound C] with n hvar
    have hnum_bound :
        (∑ i : Fin (C.theoremSetup.arrayNotation.rowLength n),
          thm_14_8_lyapunovMoment (C.theoremSetup.rowLaws n i) 2) ≤
          160 * (ex_14_4_3_couponTypes n : ℝ) := by
      rw [ex_14_4_3_row_lyapunov_sum_eq_coupon_fourth_sum C n]
      exact ex_14_4_3_fourth_moment_row_sum_is_O_n n
    have hsn_sq_lower :
        (ex_14_4_3_couponTypes n : ℝ) / 64 ≤ C.theoremSetup.sn n ^ 2 := by
      simpa [C.theoremSetup.sn_sq_eq_totalVariance n] using hvar
    have hsn_pos : 0 < C.theoremSetup.sn n := C.theoremSetup.sn_pos n
    have hden_eq :
        Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ)) =
          C.theoremSetup.sn n ^ 4 := by
      norm_num
    have hden_lower :
        ((ex_14_4_3_couponTypes n : ℝ) / 64) ^ 2 ≤
          Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ)) := by
      rw [hden_eq]
      have hsquare :
          ((ex_14_4_3_couponTypes n : ℝ) / 64) ^ 2 ≤
            (C.theoremSetup.sn n ^ 2) ^ 2 := by
        nlinarith [sq_nonneg
          (C.theoremSetup.sn n ^ 2 -
            (ex_14_4_3_couponTypes n : ℝ) / 64)]
      nlinarith
    have hden_pos :
        0 < Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ)) := by
      exact Real.rpow_pos_of_pos hsn_pos _
    have hN_pos : 0 < (ex_14_4_3_couponTypes n : ℝ) := by
      unfold ex_14_4_3_couponTypes
      positivity
    have hsmall_den_pos :
        0 < ((ex_14_4_3_couponTypes n : ℝ) / 64) ^ 2 := by
      exact sq_pos_of_pos (div_pos hN_pos (by norm_num))
    have hquot_bound :
        (∑ i : Fin (C.theoremSetup.arrayNotation.rowLength n),
          thm_14_8_lyapunovMoment (C.theoremSetup.rowLaws n i) 2) /
            Real.rpow (C.theoremSetup.sn n) (2 + (2 : ℝ)) ≤
          (160 * (ex_14_4_3_couponTypes n : ℝ)) /
            (((ex_14_4_3_couponTypes n : ℝ) / 64) ^ 2) := by
      gcongr
    have hsimplify :
        (160 * (ex_14_4_3_couponTypes n : ℝ)) /
            (((ex_14_4_3_couponTypes n : ℝ) / 64) ^ 2) =
          (160 * 4096 : ℝ) / (ex_14_4_3_couponTypes n : ℝ) := by
      field_simp [ne_of_gt hN_pos]
      ring
    simpa [q, b, hsimplify] using hquot_bound
  · have hb :
        Tendsto
          (fun n : ℕ =>
            (160 * 4096 : ℝ) / (ex_14_4_3_couponTypes n : ℝ))
          atTop (𝓝 (0 : ℝ)) := by
      simpa [Function.comp_def, ex_14_4_3_couponTypes, Nat.cast_add] using
        (tendsto_const_div_atTop_nhds_zero_nat (160 * 4096 : ℝ)).comp
          (tendsto_add_atTop_nat 2)
    simpa [b] using hb

theorem ex_14_4_3_lyapunov_condition_from_proved_bounds
    (C : ex_14_4_3_CouponTriangularArraySetup) :
    thm_14_8_LyapunovCondition C.theoremSetup :=
  ex_14_4_3_lyapunov_condition_from_fourth_moment_riemann_sum C

theorem ex_14_4_3_asymptoticNormality
    (C : ex_14_4_3_CouponTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook C.theoremSetup) :
    Tendsto C.normalizedCouponLaws atTop (𝓝 C.standardNormalLaw) := by
  have hCLT :
      thm_14_8_conclusion C.theoremSetup :=
    thm_14_8 C.theoremSetup H
      (Or.inr (ex_14_4_3_lyapunov_condition_from_proved_bounds C))
  rw [thm_14_8_conclusion, C.standardized_laws_eq, C.standard_normal_eq] at hCLT
  exact hCLT

def ex_14_4_3_TextbookNormalizedConvergence
    (C : ex_14_4_3_CouponTriangularArraySetup) : Prop :=
  ex_14_4_3_TextbookNormalization C.couponCollectionLaws C.normalizedCouponLaws ∧
    Tendsto C.normalizedCouponLaws atTop (𝓝 C.standardNormalLaw)

theorem ex_14_4_3_textbook_normalized_clt
    (C : ex_14_4_3_CouponTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook C.theoremSetup) :
    ex_14_4_3_TextbookNormalizedConvergence C := by
  exact ⟨C.textbook_normalization, ex_14_4_3_asymptoticNormality C H⟩

theorem ex_14_4_3
    (C : ex_14_4_3_CouponTriangularArraySetup)
    (H : thm_14_8_ProofBeyondBook C.theoremSetup) :
    ex_14_4_3_TextbookNormalizedConvergence C :=
  ex_14_4_3_textbook_normalized_clt C H
