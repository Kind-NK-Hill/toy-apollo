/-
TASK ID: prob_7_2
TYPE: Problem
SOURCE PLAN: 30_chap7_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

open MeasureTheory ProbabilityTheory Real Set MeasureTheory.Measure

noncomputable section

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

def IsUniform (U : Ω → ℝ) : Prop :=
  Measure.map U ℙ = volume.restrict (Icc 0 1)

def StandardBivariateNormal : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

def HasJointDist (fg : (Ω → ℝ) × (Ω → ℝ)) (ν : Measure (ℝ × ℝ)) : Prop :=
  Measure.map (fun ω => (fg.1 ω, fg.2 ω)) ℙ = ν

lemma IsUniform.aemeasurable {U : Ω → ℝ} (hU : IsUniform U) : AEMeasurable U ℙ := by
  contrapose! hU; intro h
  replace h := congr_arg (fun μ => μ Set.univ) h; simp_all +decide

def boxMullerMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.sqrt (-2 * Real.log p.1) * Real.cos (2 * π * p.2),
   Real.sqrt (-2 * Real.log p.1) * Real.sin (2 * π * p.2))

lemma boxMullerMap_measurable : Measurable boxMullerMap := by
  exact Measurable.prodMk
    (Measurable.mul
      (Measurable.sqrt (Measurable.mul measurable_const (Real.measurable_log.comp measurable_fst)))
      (Real.continuous_cos.measurable.comp (Measurable.mul measurable_const measurable_snd)))
    (Measurable.mul
      (Measurable.sqrt (Measurable.mul measurable_const (Real.measurable_log.comp measurable_fst)))
      (Real.continuous_sin.measurable.comp (Measurable.mul measurable_const measurable_snd)))

lemma map_map_of_aemeasurable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {g : β → γ} {f : α → β}
    (hg : Measurable g) (hf : AEMeasurable f μ) :
    Measure.map (g ∘ f) μ = Measure.map g (Measure.map f μ) := by
  have h1 : Measure.map (g ∘ f) μ = Measure.map (g ∘ hf.mk f) μ :=
    Measure.map_congr (hf.ae_eq_mk.fun_comp g)
  have h2 : Measure.map f μ = Measure.map (hf.mk f) μ :=
    Measure.map_congr hf.ae_eq_mk
  rw [h1, h2, Measure.map_map hg hf.measurable_mk]

lemma boxMullerMap_injOn : InjOn boxMullerMap (Ioo 0 1 ×ˢ Ioo 0 1) := by
  intro x hx y hy hxy
  have hu : x.1 = y.1 := by
    have h_log_eq :
        Real.sqrt (-2 * Real.log x.1) ^ 2 = Real.sqrt (-2 * Real.log y.1) ^ 2 := by
      have h_log :
          (Real.sqrt (-2 * Real.log x.1) * Real.cos (2 * Real.pi * x.2)) ^ 2 +
              (Real.sqrt (-2 * Real.log x.1) * Real.sin (2 * Real.pi * x.2)) ^ 2 =
            (Real.sqrt (-2 * Real.log y.1) * Real.cos (2 * Real.pi * y.2)) ^ 2 +
              (Real.sqrt (-2 * Real.log y.1) * Real.sin (2 * Real.pi * y.2)) ^ 2 := by
        exact congr_arg₂ ( · ^ 2 + · ^ 2 ) ( congr_arg Prod.fst hxy ) ( congr_arg Prod.snd hxy );
      nlinarith [ Real.sin_sq_add_cos_sq ( 2 * Real.pi * x.2 ), Real.sin_sq_add_cos_sq ( 2 * Real.pi * y.2 ) ];
    rw [ Real.sq_sqrt, Real.sq_sqrt ] at h_log_eq <;> norm_num at *;
    · rw [ ← Real.exp_log hx.1.1, ← Real.exp_log hy.1.1, h_log_eq ];
    · linarith [ Real.log_le_sub_one_of_pos hy.1.1 ];
    · linarith [ Real.log_le_sub_one_of_pos hx.1.1 ]
  have hv : x.2 = y.2 := by
    have hv : Real.cos (2 * Real.pi * x.2) = Real.cos (2 * Real.pi * y.2) ∧ Real.sin (2 * Real.pi * x.2) = Real.sin (2 * Real.pi * y.2) := by
      unfold boxMullerMap at hxy;
      norm_num [ hu ] at hxy ⊢;
      exact ⟨ hxy.1.resolve_right <| ne_of_gt <| Real.sqrt_pos.mpr <| neg_pos.mpr <| mul_neg_of_pos_of_neg zero_lt_two <| Real.log_neg hy.1.1 hy.1.2, hxy.2.resolve_right <| ne_of_gt <| Real.sqrt_pos.mpr <| neg_pos.mpr <| mul_neg_of_pos_of_neg zero_lt_two <| Real.log_neg hy.1.1 hy.1.2 ⟩;
    have hv_eq : ∃ k : ℤ, 2 * Real.pi * x.2 = 2 * Real.pi * y.2 + 2 * Real.pi * k := by
      rw [ Real.cos_eq_cos_iff, Real.sin_eq_sin_iff ] at hv;
      rcases hv.1 with ⟨ k₁, hk₁ | hk₁ ⟩ <;> rcases hv.2 with ⟨ k₂, hk₂ | hk₂ ⟩ <;> first | exact ⟨ -k₁, by push_cast; linarith ⟩ | skip;
      · exact ⟨ -k₂, by push_cast; linarith ⟩;
      · nlinarith [ Real.pi_pos, show ( k₁ : ℝ ) = k₂ by exact_mod_cast Int.le_antisymm ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.pi_pos ] } ) ( Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.pi_pos ] } ) ];
    obtain ⟨ k, hk ⟩ := hv_eq; rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos, hx.2.1, hx.2.2, hy.2.1, hy.2.2 ] ;
  aesop

lemma boxMullerMap_differentiableAt {p : ℝ × ℝ} (hp : p ∈ Ioo 0 1 ×ˢ Ioo (0:ℝ) 1) :
    DifferentiableAt ℝ boxMullerMap p := by
      apply_rules [ DifferentiableAt.prodMk, DifferentiableAt.mul, DifferentiableAt.sqrt, DifferentiableAt.log ] <;> norm_num;
      · linarith [ hp.1.1, hp.1.2 ];
      · grind;
      · linarith [ hp.1.1, hp.1.2 ];
      · exact ⟨ ne_of_gt hp.1.1, ne_of_lt hp.1.2, by linarith [ hp.1.1, hp.1.2 ] ⟩

lemma boxMullerMap_abs_det {p : ℝ × ℝ} (hp : p ∈ Ioo 0 1 ×ˢ Ioo (0:ℝ) 1) :
    |(fderiv ℝ boxMullerMap p).det| = 2 * π / p.1 := by
      have h_det : (fderiv ℝ boxMullerMap p).det = -2 * Real.pi / p.1 := by
        erw [ HasFDerivAt.fderiv ( HasFDerivAt.prodMk ( HasFDerivAt.mul ( HasFDerivAt.sqrt ( HasFDerivAt.const_mul ( HasFDerivAt.log ( hasFDerivAt_fst ) ( ne_of_gt hp.1.1 ) ) _ ) _ ) ( HasFDerivAt.cos ( HasFDerivAt.const_mul ( hasFDerivAt_snd ) _ ) ) ) ( HasFDerivAt.mul ( HasFDerivAt.sqrt ( HasFDerivAt.const_mul ( HasFDerivAt.log ( hasFDerivAt_fst ) ( ne_of_gt hp.1.1 ) ) _ ) _ ) ( HasFDerivAt.sin ( HasFDerivAt.const_mul ( hasFDerivAt_snd ) _ ) ) ) ) ] ; norm_num [ hp.1.1.ne', hp.1.2.ne', hp.2.1.ne', hp.2.2.ne', Real.pi_ne_zero, Real.sqrt_ne_zero'.mpr, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] ; ring;
        · convert LinearMap.det_toMatrix ( Pi.basisFun ℝ ( Fin 2 ) ) _ using 1;
          rotate_right;
          exact Matrix.toLin' ( Matrix.of fun i j => if i = 0 then if j = 0 then - ( Real.sqrt ( - ( Real.log p.1 * 2 ) ) ) ⁻¹ * ( 1 / 2 ) * 2 * p.1⁻¹ * Real.cos ( Real.pi * p.2 * 2 ) else Real.sqrt ( - ( Real.log p.1 * 2 ) ) * ( -Real.sin ( Real.pi * p.2 * 2 ) ) * ( Real.pi * 2 ) else if j = 0 then - ( Real.sqrt ( - ( Real.log p.1 * 2 ) ) ) ⁻¹ * ( 1 / 2 ) * 2 * p.1⁻¹ * Real.sin ( Real.pi * p.2 * 2 ) else Real.sqrt ( - ( Real.log p.1 * 2 ) ) * Real.cos ( Real.pi * p.2 * 2 ) * ( Real.pi * 2 ) );
          · norm_num [ Matrix.det_fin_two, LinearMap.toMatrix ];
            convert LinearMap.det_conj _ _ using 2;
            rotate_left;
            exact LinearEquiv.finTwoArrow ℝ ℝ;
            ext ; norm_num;
            · norm_num [ Matrix.vecHead, Matrix.vecTail ] ; ring;
            · norm_num [ Matrix.vecHead, Matrix.vecTail ] ; ring;
            · norm_num [ Matrix.vecHead, Matrix.vecTail ] ; ring;
            · norm_num [ Matrix.vecHead, Matrix.vecTail ] ; ring;
          · norm_num [ Matrix.det_fin_two ] ; ring;
            rw [ Real.sin_sq, Real.cos_sq ] ; ring;
            rw [ mul_inv_cancel_right₀ ( ne_of_gt ( Real.sqrt_pos.mpr ( neg_pos.mpr ( mul_neg_of_neg_of_pos ( Real.log_neg hp.1.1 hp.1.2 ) zero_lt_two ) ) ) ) ];
        · exact mul_ne_zero ( by norm_num ) ( ne_of_lt ( Real.log_neg hp.1.1 hp.1.2 ) );
        · exact mul_ne_zero ( by norm_num ) ( ne_of_lt ( Real.log_neg hp.1.1 hp.1.2 ) );
      rw [ h_det, abs_div, abs_mul, abs_neg, abs_two, abs_of_nonneg ( le_of_lt ( Real.pi_pos ) ), abs_of_nonneg ( le_of_lt ( hp.1.1 ) ) ]

lemma boxMullerMap_image_ae :
    (volume : Measure (ℝ × ℝ)) (univ \ boxMullerMap '' (Ioo 0 1 ×ˢ Ioo 0 1)) = 0 := by
      refine' MeasureTheory.measure_mono_null _ _;
      exact Set.univ ×ˢ { 0 } ∪ { 0 } ×ˢ Set.univ ∪ { ( 0, 0 ) };
      · intro p hp
        simp [Set.mem_diff, Set.mem_image] at hp
        generalize_proofs at *; (
        contrapose! hp; simp_all +decide [ boxMullerMap ] ; (
        -- Let `r = sqrt(p.1^2 + p.2^2)` and `theta = arg(p.1 + p.2 i)`.
        obtain ⟨r, hr⟩ : ∃ r : ℝ, 0 < r ∧ r = Real.sqrt (p.1^2 + p.2^2) := by
          exact ⟨ _, Real.sqrt_pos.mpr ( by nlinarith [ mul_self_pos.mpr hp.1, mul_self_pos.mpr hp.2 ] ), rfl ⟩
        obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ θ < 2 * Real.pi ∧ p.1 = r * Real.cos θ ∧ p.2 = r * Real.sin θ := by
          obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, p.1 = r * Real.cos θ ∧ p.2 = r * Real.sin θ := by
            use ( Complex.arg ( p.1 + p.2 * Complex.I ) );
            rw [ Complex.cos_arg, Complex.sin_arg ] <;> simp_all +decide [ Complex.ext_iff ];
            norm_num [ Complex.normSq, Complex.norm_def, ← sq, hr.2 ];
            exact ⟨ by rw [ mul_div_cancel₀ _ ( ne_of_gt ( Real.sqrt_pos.mpr ( by nlinarith [ mul_self_pos.mpr hp.1, mul_self_pos.mpr hp.2 ] ) ) ) ], by rw [ mul_div_cancel₀ _ ( ne_of_gt ( Real.sqrt_pos.mpr ( by nlinarith [ mul_self_pos.mpr hp.1, mul_self_pos.mpr hp.2 ] ) ) ) ] ⟩;
          exact ⟨ θ - 2 * Real.pi * ⌊θ / ( 2 * Real.pi ) ⌋, by nlinarith [ Int.floor_le ( θ / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ θ ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ], by nlinarith [ Int.lt_floor_add_one ( θ / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ θ ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ], by simpa [ mul_comm ( 2 * Real.pi ) ] using hθ ⟩;
        refine' ⟨ Real.exp ( -r ^ 2 / 2 ), _, _, θ / ( 2 * Real.pi ), _, _, _ ⟩ <;> norm_num [ Real.exp_pos, hr.1, hθ.1, hθ.2.1 ];
        · nlinarith [ mul_self_pos.2 hr.1.ne' ];
        · exact div_pos ( lt_of_le_of_ne hθ.1 ( Ne.symm <| by rintro rfl; norm_num at hθ; tauto ) ) ( by positivity );
        · rw [ div_lt_iff₀ ] <;> linarith;
        · grind +splitIndPred););
      · erw [ MeasureTheory.measure_union_null ] <;> norm_num [ MeasureTheory.MeasureSpace.volume ]

lemma restrict_Icc_eq_restrict_Ioo_ae :
    (volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict (Icc (0:ℝ) 1)) =
    (volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) 1)) := by
      rw [ MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc ]

lemma gaussianReal_prod_eq_withDensity :
    (gaussianReal 0 1).prod (gaussianReal 0 1) =
    (volume : Measure (ℝ × ℝ)).withDensity
      (fun p => ENNReal.ofReal ((2 * π)⁻¹ * rexp (-(p.1 ^ 2 + p.2 ^ 2) / 2))) := by
        have h_prod : (gaussianReal 0 1).prod (gaussianReal 0 1) = Measure.prod (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)))) (volume.withDensity (fun y => ENNReal.ofReal (Real.exp (-y^2 / 2) / Real.sqrt (2 * Real.pi)))) := by
          unfold gaussianReal;
          unfold gaussianPDF; norm_num [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm, Real.pi_pos.le ] ;
          unfold gaussianPDFReal; norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Real.pi_pos.le ] ;
        convert h_prod using 1;
        rw [ MeasureTheory.Measure.prod_eq ];
        intro s t hs ht;
        erw [ MeasureTheory.withDensity_apply' ];
        erw [ MeasureTheory.setLIntegral_prod ];
        · rw [ MeasureTheory.withDensity_apply' ];
          rw [ MeasureTheory.withDensity_apply' ];
          rw [ ← MeasureTheory.lintegral_lintegral_mul ];
          · refine' MeasureTheory.lintegral_congr fun x => MeasureTheory.lintegral_congr fun y => _;
            rw [ ← ENNReal.ofReal_mul ( by positivity ) ] ; ring;
            rw [ inv_pow, Real.sq_sqrt <| by positivity ] ; rw [ Real.exp_add ] ; ring;
          · exact Measurable.aemeasurable ( by exact Measurable.ennreal_ofReal ( by exact Measurable.div_const ( Real.continuous_exp.measurable.comp ( by exact Continuous.measurable ( by continuity ) ) ) _ ) );
          · exact Measurable.aemeasurable ( by exact Measurable.ennreal_ofReal ( by exact Measurable.div_const ( Real.continuous_exp.measurable.comp ( by exact Continuous.measurable ( by continuity ) ) ) _ ) );
        · fun_prop

lemma boxMuller_pushforward_uniform :
    Measure.map boxMullerMap ((volume.restrict (Icc 0 1)).prod (volume.restrict (Icc 0 1))) =
    (gaussianReal 0 1).prod (gaussianReal 0 1) := by
      rw [ gaussianReal_prod_eq_withDensity, restrict_Icc_eq_restrict_Ioo_ae ];
      apply Measure.ext;
      intro s hs
      have h_eq : (Measure.map boxMullerMap (Measure.prod (Measure.restrict MeasureSpace.volume (Set.Ioo 0 1)) (Measure.restrict MeasureSpace.volume (Set.Ioo 0 1)))) s = (Measure.restrict MeasureSpace.volume (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)) (boxMullerMap ⁻¹' s) := by
        rw [ MeasureTheory.Measure.map_apply ] <;> norm_num [ hs, boxMullerMap_measurable ];
        rw [ MeasureTheory.Measure.prod_restrict ];
        rfl;
      have h_eq : (Measure.restrict MeasureSpace.volume (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)) (boxMullerMap ⁻¹' s) = ∫⁻ p in (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) ∩ boxMullerMap ⁻¹' s, 1 ∂MeasureSpace.volume := by
        simp +decide [ Set.inter_comm ];
        rw [ MeasureTheory.Measure.restrict_apply ];
        · grind;
        · exact measurableSet_preimage ( boxMullerMap_measurable ) hs;
      have h_eq : ∫⁻ p in (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) ∩ boxMullerMap ⁻¹' s, 1 ∂MeasureSpace.volume = ∫⁻ x in boxMullerMap '' ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) ∩ boxMullerMap ⁻¹' s), ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / 2)) ∂MeasureSpace.volume := by
        rw [ MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul ];
        rotate_right;
        use fun p => fderiv ℝ boxMullerMap p;
        · refine' MeasureTheory.setLIntegral_congr_fun _ _;
          · exact MeasurableSet.inter ( measurableSet_Ioo.prod measurableSet_Ioo ) ( measurableSet_preimage ( show Measurable boxMullerMap from by exact boxMullerMap_measurable ) hs );
          · intro p hp; simp_all +decide [ boxMullerMap_abs_det ];
            rw [ ← ENNReal.ofReal_mul ( by exact div_nonneg ( by positivity ) ( by linarith ) ) ] ; ring_nf ; norm_num [ Real.pi_pos.ne' ];
            unfold boxMullerMap; norm_num [ mul_assoc, mul_comm Real.pi _, Real.pi_ne_zero ] ; ring_nf ; norm_num [ Real.pi_pos.ne', hp.1.1.1.ne', hp.1.1.2.ne' ] ;
            rw [ Real.sq_sqrt ( by nlinarith [ Real.log_le_sub_one_of_pos hp.1.1.1 ] ) ] ; norm_num [ Real.sin_sq, Real.cos_sq ] ; ring_nf ; norm_num [ hp.1.1.1.ne', hp.1.1.2.ne', Real.exp_neg, Real.exp_log hp.1.1.1 ];
        · exact MeasurableSet.inter ( measurableSet_Ioo.prod measurableSet_Ioo ) ( measurableSet_preimage ( show Measurable boxMullerMap from by exact boxMullerMap_measurable ) hs );
        · exact fun x hx => DifferentiableAt.hasFDerivAt ( boxMullerMap_differentiableAt hx.1 ) |> HasFDerivAt.hasFDerivWithinAt;
        · exact fun x hx y hy hxy => boxMullerMap_injOn ( by aesop ) ( by aesop ) hxy;
      have h_eq : boxMullerMap '' ((Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) ∩ boxMullerMap ⁻¹' s) = s \ (univ \ boxMullerMap '' (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1)) := by
        grind +locals;
      have h_eq : (MeasureSpace.volume (univ \ boxMullerMap '' (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1))) = 0 := by
        convert boxMullerMap_image_ae using 1;
      simp_all +decide [ MeasureTheory.withDensity_apply ];
      rw [ MeasureTheory.Measure.restrict_congr_set ];
      exact diff_null_ae_eq_self h_eq

theorem prob_7_2 (U V : Ω → ℝ) (hU : IsUniform U) (hV : IsUniform V) (hindep : IndepFun U V) :
    let X := fun ω => Real.sqrt (-2 * Real.log (U ω)) * Real.cos (2 * π * V ω)
    let Y := fun ω => Real.sqrt (-2 * Real.log (U ω)) * Real.sin (2 * π * V ω)
    HasJointDist (X, Y) StandardBivariateNormal := by
  intro X Y
  show Measure.map (fun ω => (X ω, Y ω)) ℙ = (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hcomp : (fun ω => (X ω, Y ω)) = boxMullerMap ∘ (fun ω => (U ω, V ω)) := rfl
  rw [hcomp]
  have hprod_ae : AEMeasurable (fun ω => (U ω, V ω)) ℙ :=
    hU.aemeasurable.prodMk hV.aemeasurable
  rw [map_map_of_aemeasurable boxMullerMap_measurable hprod_ae]
  have hjoint : Measure.map (fun ω => (U ω, V ω)) ℙ =
    (Measure.map U ℙ).prod (Measure.map V ℙ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).mp hindep
  rw [hjoint, hU, hV]
  exact boxMuller_pushforward_uniform

end
