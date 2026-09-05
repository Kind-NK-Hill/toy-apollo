/-
TASK ID: ex_14_3_2
TYPE: Example_Proof
SOURCE PLAN: chapter14-prokhorov-sequential-compactness
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_14.thm_14_1




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section



def ex_14_3_2_pn (lam : ℝ) (n : ℕ) : ℝ :=
  lam / (n + 1 : ℝ)

 
lemma ex_14_3_2_index_ne_zero (n : ℕ) : ((n : ℂ) + 1) ≠ 0 := by
  have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  simpa [Nat.cast_add, Nat.cast_one] using h



def ex_14_3_2_scaledGeometricCharacteristic_source
    (lam : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  let N : ℂ := (n : ℂ) + 1
  let s : ℂ := Complex.I * (t : ℂ)
  (((lam : ℂ) / N) * Complex.exp (s / N)) /
    (1 - (1 - (lam : ℂ) / N) * Complex.exp (s / N))



def ex_14_3_2_scaledGeometricCharacteristic
    (lam : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  let N : ℂ := (n : ℂ) + 1
  let s : ℂ := Complex.I * (t : ℂ)
  let E : ℂ := Complex.exp (s / N)
  (lam : ℂ) * E / (N * (1 - (1 - (lam : ℂ) / N) * E))

 
theorem ex_14_3_2_scaledGeometricCharacteristic_source_form
    (lam : ℝ) (n : ℕ) (t : ℝ) :
    ex_14_3_2_scaledGeometricCharacteristic lam n t =
      ex_14_3_2_scaledGeometricCharacteristic_source lam n t := by
  unfold ex_14_3_2_scaledGeometricCharacteristic
    ex_14_3_2_scaledGeometricCharacteristic_source
  have hN := ex_14_3_2_index_ne_zero n
  field_simp [hN]



def ex_14_3_2_exponentialCharacteristic (lam : ℝ) (t : ℝ) : ℂ :=
  (lam : ℂ) / ((lam : ℂ) - Complex.I * (t : ℂ))

 
lemma ex_14_3_2_inv_index_tendsto :
    Tendsto (fun n : ℕ => (((n : ℂ) + 1)⁻¹)) atTop (𝓝 (0 : ℂ)) := by
  simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))



theorem ex_14_3_2_index_mul_exp_sub_one_tendsto (s : ℂ) :
    Tendsto
      (fun n : ℕ =>
        ((n : ℂ) + 1) * (Complex.exp (s / ((n : ℂ) + 1)) - 1))
      atTop (𝓝 s) := by
  by_cases hs : s = 0
  · subst s
    simp
  · have hInv := ex_14_3_2_inv_index_tendsto
    have hU_nhds :
        Tendsto (fun n : ℕ => s / ((n : ℂ) + 1)) atTop (𝓝 (0 : ℂ)) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul hInv :
          Tendsto (fun n : ℕ => s * (((n : ℂ) + 1)⁻¹))
            atTop (𝓝 (s * 0)))
    have hU_ne :
        ∀ᶠ n : ℕ in atTop, s / ((n : ℂ) + 1) ∈ ({0}ᶜ : Set ℂ) := by
      filter_upwards with n
      have hN := ex_14_3_2_index_ne_zero n
      simp [hs, hN]
    have hU :
        Tendsto (fun n : ℕ => s / ((n : ℂ) + 1))
          atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hU_nhds, hU_ne⟩
    have hSlope :
        Tendsto
          (fun n : ℕ =>
            (s / ((n : ℂ) + 1))⁻¹ •
              (Complex.exp (0 + s / ((n : ℂ) + 1)) -
                Complex.exp (0 : ℂ)))
          atTop (𝓝 (1 : ℂ)) := by
      simpa [Function.comp_def] using
        ((Complex.hasDerivAt_exp 0).tendsto_slope_zero.comp hU)
    have hScaled :
        Tendsto
          (fun n : ℕ =>
            s * ((s / ((n : ℂ) + 1))⁻¹ *
              (Complex.exp (s / ((n : ℂ) + 1)) - 1)))
          atTop (𝓝 (s * 1)) := by
      simpa [zero_add, Complex.exp_zero] using
        (tendsto_const_nhds.mul hSlope :
          Tendsto
            (fun n : ℕ =>
              s * ((s / ((n : ℂ) + 1))⁻¹ •
                (Complex.exp (0 + s / ((n : ℂ) + 1)) -
                  Complex.exp (0 : ℂ))))
            atTop (𝓝 (s * 1)))
    have hScaled' :
        Tendsto
          (fun n : ℕ =>
            ((n : ℂ) + 1) *
              (Complex.exp (s / ((n : ℂ) + 1)) - 1))
          atTop (𝓝 (s * 1)) := by
      refine Filter.Tendsto.congr' ?_ hScaled
      filter_upwards with n
      have hN := ex_14_3_2_index_ne_zero n
      field_simp [hs, hN]
    simpa using hScaled'



theorem ex_14_3_2_denominator_tendsto (lam : ℝ) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        let N : ℂ := (n : ℂ) + 1
        let s : ℂ := Complex.I * (t : ℂ)
        let E : ℂ := Complex.exp (s / N)
        N * (1 - (1 - (lam : ℂ) / N) * E))
      atTop (𝓝 ((lam : ℂ) - Complex.I * (t : ℂ))) := by
  let s : ℂ := Complex.I * (t : ℂ)
  have hNE := ex_14_3_2_index_mul_exp_sub_one_tendsto s
  have hInv := ex_14_3_2_inv_index_tendsto
  have hU_nhds :
      Tendsto (fun n : ℕ => s / ((n : ℂ) + 1)) atTop (𝓝 (0 : ℂ)) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hInv :
        Tendsto (fun n : ℕ => s * (((n : ℂ) + 1)⁻¹))
          atTop (𝓝 (s * 0)))
  have hE :
      Tendsto (fun n : ℕ => Complex.exp (s / ((n : ℂ) + 1)))
        atTop (𝓝 (1 : ℂ)) := by
    change Tendsto (Complex.exp ∘ fun n : ℕ => s / ((n : ℂ) + 1))
      atTop (𝓝 (1 : ℂ))
    simpa only [Complex.exp_zero] using
      (Complex.continuous_exp.continuousAt.tendsto.comp hU_nhds)
  have hLamE :
      Tendsto
        (fun n : ℕ => (lam : ℂ) * Complex.exp (s / ((n : ℂ) + 1)))
        atTop (𝓝 ((lam : ℂ) * 1)) :=
    tendsto_const_nhds.mul hE
  have hDenAux :
      Tendsto
        (fun n : ℕ =>
          - (((n : ℂ) + 1) *
              (Complex.exp (s / ((n : ℂ) + 1)) - 1)) +
            (lam : ℂ) * Complex.exp (s / ((n : ℂ) + 1)))
        atTop (𝓝 (-s + (lam : ℂ) * 1)) :=
    hNE.neg.add hLamE
  have hDenAux' :
      Tendsto
        (fun n : ℕ =>
          let N : ℂ := (n : ℂ) + 1
          let s : ℂ := Complex.I * (t : ℂ)
          let E : ℂ := Complex.exp (s / N)
          N * (1 - (1 - (lam : ℂ) / N) * E))
        atTop (𝓝 (-s + (lam : ℂ) * 1)) := by
    refine Filter.Tendsto.congr' ?_ hDenAux
    filter_upwards with n
    have hN := ex_14_3_2_index_ne_zero n
    dsimp [s]
    field_simp [hN]
    ring
  simpa [s, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hDenAux'



lemma ex_14_3_2_exponential_denominator_ne_zero
    {lam : ℝ} (hpos : 0 < lam) (t : ℝ) :
    ((lam : ℂ) - Complex.I * (t : ℂ)) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp at hre
  linarith

 
theorem ex_14_3_2_scaledGeometricCharacteristic_tendsto
    {lam : ℝ} (hpos : 0 < lam) (t : ℝ) :
    Tendsto
      (fun n : ℕ => ex_14_3_2_scaledGeometricCharacteristic lam n t)
      atTop (𝓝 (ex_14_3_2_exponentialCharacteristic lam t)) := by
  let s : ℂ := Complex.I * (t : ℂ)
  have hInv := ex_14_3_2_inv_index_tendsto
  have hU_nhds :
      Tendsto (fun n : ℕ => s / ((n : ℂ) + 1)) atTop (𝓝 (0 : ℂ)) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hInv :
        Tendsto (fun n : ℕ => s * (((n : ℂ) + 1)⁻¹))
          atTop (𝓝 (s * 0)))
  have hE :
      Tendsto (fun n : ℕ => Complex.exp (s / ((n : ℂ) + 1)))
        atTop (𝓝 (1 : ℂ)) := by
    change Tendsto (Complex.exp ∘ fun n : ℕ => s / ((n : ℂ) + 1))
      atTop (𝓝 (1 : ℂ))
    simpa only [Complex.exp_zero] using
      (Complex.continuous_exp.continuousAt.tendsto.comp hU_nhds)
  have hNum :
      Tendsto
        (fun n : ℕ => (lam : ℂ) * Complex.exp (s / ((n : ℂ) + 1)))
        atTop (𝓝 ((lam : ℂ) * 1)) :=
    tendsto_const_nhds.mul hE
  have hDen := ex_14_3_2_denominator_tendsto lam t
  have hDenNe := ex_14_3_2_exponential_denominator_ne_zero hpos t
  have hDiv := hNum.div hDen hDenNe
  have hDiv' :
      Tendsto
        (fun n : ℕ => ex_14_3_2_scaledGeometricCharacteristic lam n t)
        atTop
        (𝓝 (((lam : ℂ) * 1) / ((lam : ℂ) - Complex.I * (t : ℂ)))) := by
    refine Filter.Tendsto.congr' ?_ hDiv
    filter_upwards with n
    rfl
  simpa [ex_14_3_2_exponentialCharacteristic] using hDiv'



structure ex_14_3_2_GeometricExponentialSetup (lam : ℝ) where
  positive_lambda : 0 < lam
  scaledGeometricLaws : ℕ → ProbabilityMeasure ℝ
  exponentialLaw : ProbabilityMeasure ℝ
  scaled_geometric_characteristic :
    ∀ n : ℕ, ∀ t : ℝ,
      thm_14_1_characteristicFunction (scaledGeometricLaws n) t =
        ex_14_3_2_scaledGeometricCharacteristic lam n t
  exponential_characteristic :
    ∀ t : ℝ,
      thm_14_1_characteristicFunction exponentialLaw t =
        ex_14_3_2_exponentialCharacteristic lam t



theorem ex_14_3_2_pointwiseCharacteristicConvergence
    {lam : ℝ} (S : ex_14_3_2_GeometricExponentialSetup lam) :
    thm_14_1_pointwiseCharFunConvergence S.scaledGeometricLaws
      (fun t : ℝ => thm_14_1_characteristicFunction S.exponentialLaw t) := by
  intro t
  have hlimit :=
    ex_14_3_2_scaledGeometricCharacteristic_tendsto S.positive_lambda t
  have hleft :
      (fun n : ℕ =>
        thm_14_1_characteristicFunction (S.scaledGeometricLaws n) t) =
        fun n : ℕ => ex_14_3_2_scaledGeometricCharacteristic lam n t := by
    funext n
    simpa using S.scaled_geometric_characteristic n t
  have hright :
      ex_14_3_2_exponentialCharacteristic lam t =
        thm_14_1_characteristicFunction S.exponentialLaw t :=
    (S.exponential_characteristic t).symm
  simpa [hleft, hright] using hlimit



theorem ex_14_3_2_converges_to_exponential
    {lam : ℝ} (S : ex_14_3_2_GeometricExponentialSetup lam) :
    Tendsto S.scaledGeometricLaws atTop (𝓝 S.exponentialLaw) := by
  have hchar := ex_14_3_2_pointwiseCharacteristicConvergence S
  exact (ProbabilityMeasure.tendsto_iff_tendsto_charFun).2 (fun t : ℝ => by
    simpa [thm_14_1_characteristicFunction] using hchar t)



theorem ex_14_3_2_weakLimit_by_Levy
    {lam : ℝ} (S : ex_14_3_2_GeometricExponentialSetup lam) :
    thm_14_1_weakLimit S.scaledGeometricLaws := by
  have hchar := ex_14_3_2_pointwiseCharacteristicConvergence S
  exact (thm_14_1_weak_iff_characteristic hchar).2
    ⟨S.exponentialLaw, fun _ => rfl⟩



theorem ex_14_3_2
    {lam : ℝ} (S : ex_14_3_2_GeometricExponentialSetup lam) :
    Tendsto S.scaledGeometricLaws atTop (𝓝 S.exponentialLaw) :=
  ex_14_3_2_converges_to_exponential S
