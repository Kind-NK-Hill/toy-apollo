/-
TASK ID: thm_14_8
TYPE: Theorem_Statement
SOURCE PLAN: chapter14-central-limit-theorems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_14_7_support
import ToyApollo.Output.ex_14_4_2

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

namespace Thm148Core

structure Setup where
  arrayNotation : chapter14_TriangularArrayNotation
  rowLaws : (n : ℕ) → Fin (arrayNotation.rowLength n) → ProbabilityMeasure ℝ
  row_sq_integrable :
    ∀ n : ℕ, ∀ i : Fin (arrayNotation.rowLength n),
      Integrable (fun x : ℝ ↦ x ^ 2) (rowLaws n i : Measure ℝ)
  row_mean_zero :
    ∀ n : ℕ, ∀ i : Fin (arrayNotation.rowLength n),
      ∫ x, x ∂(rowLaws n i : Measure ℝ) = 0
  row_variance :
    ∀ n : ℕ, ∀ i : Fin (arrayNotation.rowLength n),
      arrayNotation.variance n i =
        ∫ x, x ^ 2 ∂(rowLaws n i : Measure ℝ)
  totalVariance_pos : ∀ n : ℕ, 0 < arrayNotation.totalVariance n

namespace Setup

def sn (S : Setup) (n : ℕ) : ℝ :=
  Real.sqrt (S.arrayNotation.totalVariance n)

theorem sn_pos (S : Setup) (n : ℕ) : 0 < S.sn n := by
  exact Real.sqrt_pos.2 (S.totalVariance_pos n)

theorem sn_sq_eq_totalVariance (S : Setup) (n : ℕ) :
    S.sn n ^ 2 = S.arrayNotation.totalVariance n := by
  exact Real.sq_sqrt (le_of_lt (S.totalVariance_pos n))

theorem sn_tendsto_atTop (S : Setup) :
    Tendsto S.sn atTop atTop := by
  exact Real.tendsto_sqrt_atTop.comp
    S.arrayNotation.totalVariance_tendsto_atTop

def rowProductLaw (S : Setup) (n : ℕ) :
    ProbabilityMeasure (Fin (S.arrayNotation.rowLength n) → ℝ) :=
  ProbabilityMeasure.pi (S.rowLaws n)

def rowCoordinate (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) :
    (Fin (S.arrayNotation.rowLength n) → ℝ) → ℝ :=
  fun x ↦ x i

theorem rowCoordinate_aemeasurable (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) :
    AEMeasurable (S.rowCoordinate n i) (S.rowProductLaw n : Measure _) := by
  change AEMeasurable
    (fun x : Fin (S.arrayNotation.rowLength n) → ℝ ↦ x i)
    (S.rowProductLaw n : Measure _)
  exact (measurable_pi_apply i).aemeasurable

theorem rowCoordinate_law (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) :
    thm_14_7_law (S.rowProductLaw n : Measure _)
        (S.rowCoordinate n i) (S.rowCoordinate_aemeasurable n i) =
      S.rowLaws n i := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.pi (fun j ↦ (S.rowLaws n j : Measure ℝ))).map
      (Function.eval i) = (S.rowLaws n i : Measure ℝ)
  exact MeasureTheory.measurePreserving_eval
    (fun j ↦ (S.rowLaws n j : Measure ℝ)) i |>.map_eq

theorem rowCoordinate_iIndep (S : Setup) (n : ℕ) :
    ProbabilityTheory.iIndepFun (S.rowCoordinate n)
      (S.rowProductLaw n : Measure _) := by
  change ProbabilityTheory.iIndepFun
    (fun i (x : Fin (S.arrayNotation.rowLength n) → ℝ) ↦ x i)
    (Measure.pi (fun i ↦ (S.rowLaws n i : Measure ℝ)))
  exact ProbabilityTheory.iIndepFun_pi
    (X := fun _ : Fin (S.arrayNotation.rowLength n) ↦ id)
    (fun _ ↦ aemeasurable_id)

def standardizedSum (S : Setup) (n : ℕ) :
    (Fin (S.arrayNotation.rowLength n) → ℝ) → ℝ :=
  fun x ↦ (∑ i, x i) / S.sn n

theorem standardizedSum_aemeasurable (S : Setup) (n : ℕ) :
    AEMeasurable (S.standardizedSum n) (S.rowProductLaw n : Measure _) := by
  change AEMeasurable
    (fun x : Fin (S.arrayNotation.rowLength n) → ℝ ↦
      (∑ i, x i) / S.sn n)
    (S.rowProductLaw n : Measure _)
  fun_prop

def standardizedSumLaw (S : Setup) (n : ℕ) : ProbabilityMeasure ℝ :=
  thm_14_7_law (S.rowProductLaw n : Measure _) (S.standardizedSum n)
    (S.standardizedSum_aemeasurable n)

abbrev standardNormalLaw : ProbabilityMeasure ℝ :=
  thm_14_7_standardNormalLaw

theorem standardizedSumCharacteristic_eq_prod (S : Setup) (n : ℕ) (t : ℝ) :
    thm_14_1_characteristicFunction (S.standardizedSumLaw n) t =
      ∏ i : Fin (S.arrayNotation.rowLength n),
        thm_14_1_characteristicFunction (S.rowLaws n i) (t / S.sn n) := by
  have hstandardized :
      S.standardizedSum n =
        fun x : Fin (S.arrayNotation.rowLength n) → ℝ ↦
          (S.sn n)⁻¹ * ∑ i, x i := by
    funext x
    simp only [standardizedSum, div_eq_mul_inv]
    ring
  have hscale := thm_14_7_characteristicFunction_const_mul
    (P := (S.rowProductLaw n : Measure _))
    (Y := fun x : Fin (S.arrayNotation.rowLength n) → ℝ ↦ ∑ i, x i)
    (by fun_prop) (S.sn n)⁻¹ t
  have hprod := congrFun
    (ProbabilityTheory.charFun_map_sum_pi_eq_prod
      (fun i : Fin (S.arrayNotation.rowLength n) ↦
        (S.rowLaws n i : Measure ℝ)))
    ((S.sn n)⁻¹ * t)
  calc
    thm_14_1_characteristicFunction (S.standardizedSumLaw n) t =
        thm_14_1_characteristicFunction
          (thm_14_7_law (S.rowProductLaw n : Measure _)
            (fun x : Fin (S.arrayNotation.rowLength n) → ℝ ↦ ∑ i, x i)
            (by fun_prop))
          ((S.sn n)⁻¹ * t) := by
            change charFun
                ((S.rowProductLaw n : Measure _).map (S.standardizedSum n)) t =
              charFun
                ((S.rowProductLaw n : Measure _).map
                  (fun x : Fin (S.arrayNotation.rowLength n) → ℝ ↦ ∑ i, x i))
                ((S.sn n)⁻¹ * t)
            rw [hstandardized]
            unfold thm_14_1_characteristicFunction thm_14_7_law at hscale
            simpa [mul_comm] using hscale
    _ = ∏ i : Fin (S.arrayNotation.rowLength n),
          thm_14_1_characteristicFunction (S.rowLaws n i)
            ((S.sn n)⁻¹ * t) := by
          simpa [thm_14_1_characteristicFunction, thm_14_7_law,
            rowProductLaw] using hprod
    _ = ∏ i : Fin (S.arrayNotation.rowLength n),
          thm_14_1_characteristicFunction (S.rowLaws n i)
            (t / S.sn n) := by
          congr 1
          funext i
          rw [div_eq_mul_inv, mul_comm]

end Setup

end Thm148Core

namespace Thm148ConcreteBridge

theorem map_normalizedSum_eq_pi_of_iIndep
    {Omega : Type*} [MeasurableSpace Omega]
    {k : Nat} (P : Measure Omega) [IsProbabilityMeasure P]
    (X : Fin k -> Omega -> Real)
    (hX : forall i : Fin k, AEMeasurable (X i) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (mu : Fin k -> ProbabilityMeasure Real)
    (hMarginal : forall i : Fin k, P.map (X i) = (mu i : Measure Real))
    (s : Real) :
    P.map (fun omega => (Finset.univ.sum fun i : Fin k => X i omega) / s) =
      (Measure.pi (fun i : Fin k => (mu i : Measure Real))).map
        (fun x => (Finset.univ.sum fun i : Fin k => x i) / s) := by
  let joint : Omega -> (Fin k -> Real) := fun omega i => X i omega
  let normalize : (Fin k -> Real) -> Real :=
    fun x => (Finset.univ.sum fun i : Fin k => x i) / s
  have hJointMeas : AEMeasurable joint P := by
    exact aemeasurable_pi_lambda joint (fun i => hX i)
  have hNormalizeMeas : Measurable normalize := by
    dsimp [normalize]
    fun_prop
  have hJointLaw :
      P.map joint = Measure.pi (fun i : Fin k => (mu i : Measure Real)) := by
    calc
      P.map joint = Measure.pi (fun i : Fin k => P.map (X i)) := by
        simpa [joint] using hIndep.map_fun_eq_pi_map hX
      _ = Measure.pi (fun i : Fin k => (mu i : Measure Real)) := by
        congr 1
        funext i
        exact hMarginal i
  calc
    P.map (fun omega => (Finset.univ.sum fun i : Fin k => X i omega) / s) =
        P.map (normalize ∘ joint) := by rfl
    _ = (P.map joint).map normalize :=
      (AEMeasurable.map_map_of_aemeasurable
        hNormalizeMeas.aemeasurable hJointMeas).symm
    _ = (Measure.pi (fun i : Fin k => (mu i : Measure Real))).map
        normalize := by rw [hJointLaw]
    _ = (Measure.pi (fun i : Fin k => (mu i : Measure Real))).map
        (fun x => (Finset.univ.sum fun i : Fin k => x i) / s) := by rfl

theorem concrete_standardizedSum_map_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (S : Thm148Core.Setup) (n : Nat)
    (X : Fin (S.arrayNotation.rowLength n) -> Omega -> Real)
    (hX : forall i : Fin (S.arrayNotation.rowLength n),
      AEMeasurable (X i) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hLaw : forall i : Fin (S.arrayNotation.rowLength n),
      thm_14_7_law P (X i) (hX i) = S.rowLaws n i) :
    P.map
        (fun omega =>
          (Finset.univ.sum
            fun i : Fin (S.arrayNotation.rowLength n) => X i omega) /
              S.sn n) =
      (S.standardizedSumLaw n : Measure Real) := by
  have hMarginal : forall i : Fin (S.arrayNotation.rowLength n),
      P.map (X i) = (S.rowLaws n i : Measure Real) := by
    intro i
    simpa [thm_14_7_law] using
      congrArg ProbabilityMeasure.toMeasure (hLaw i)
  have h := map_normalizedSum_eq_pi_of_iIndep
    P X hX hIndep (S.rowLaws n) hMarginal (S.sn n)
  change P.map
      (fun omega =>
        (Finset.univ.sum
          fun i : Fin (S.arrayNotation.rowLength n) => X i omega) /
            S.sn n) =
    (Measure.pi
      (fun i : Fin (S.arrayNotation.rowLength n) =>
        (S.rowLaws n i : Measure Real))).map
      (fun x =>
        (Finset.univ.sum
          fun i : Fin (S.arrayNotation.rowLength n) => x i) /
            S.sn n)
  exact h

theorem concrete_standardizedSum_law_eq
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (S : Thm148Core.Setup) (n : Nat)
    (X : Fin (S.arrayNotation.rowLength n) -> Omega -> Real)
    (hX : forall i : Fin (S.arrayNotation.rowLength n),
      AEMeasurable (X i) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hLaw : forall i : Fin (S.arrayNotation.rowLength n),
      thm_14_7_law P (X i) (hX i) = S.rowLaws n i) :
    thm_14_7_law P
        (fun omega =>
          (Finset.univ.sum
            fun i : Fin (S.arrayNotation.rowLength n) => X i omega) /
              S.sn n)
        (by fun_prop) =
      S.standardizedSumLaw n := by
  apply ProbabilityMeasure.toMeasure_injective
  change P.map
      (fun omega =>
        (Finset.univ.sum
          fun i : Fin (S.arrayNotation.rowLength n) => X i omega) /
            S.sn n) =
    (S.standardizedSumLaw n : Measure Real)
  exact concrete_standardizedSum_map_eq P S n X hX hIndep hLaw

end Thm148ConcreteBridge

open scoped ComplexConjugate

namespace Thm148Product

noncomputable section

def q (u : ℝ) : ℂ :=
  Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I + (u : ℂ) ^ 2 / 2

lemma q_eq_exp_sub_taylor (u : ℝ) :
    q u = Complex.exp ((u : ℂ) * Complex.I) -
      ∑ m ∈ Finset.range 3, (((u : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) := by
  simp [q, Finset.sum_range_succ]
  rw [mul_pow, Complex.I_sq]
  ring

lemma norm_real_mul_I (u : ℝ) : ‖(u : ℂ) * Complex.I‖ = |u| := by
  simp [Real.norm_eq_abs]

lemma norm_q_le_abs_pow_three {u : ℝ} (hu : |u| ≤ 1) :
    ‖q u‖ ≤ |u| ^ 3 := by
  have h := Complex.exp_bound (x := (u : ℂ) * Complex.I) (n := 3) (by simpa [norm_real_mul_I] using hu)
    (by norm_num)
  rw [← q_eq_exp_sub_taylor] at h
  norm_num [norm_real_mul_I] at h ⊢
  calc
    ‖q u‖ ≤ |u| ^ 3 * (2 / 9) := h
    _ ≤ |u| ^ 3 := by
      exact mul_le_of_le_one_right (pow_nonneg (abs_nonneg u) 3) (by norm_num)

lemma exp_neg_sub_linear_eq_taylor (a : ℝ) :
    Complex.exp (-(a : ℂ)) - (1 - (a : ℂ)) =
      Complex.exp (-(a : ℂ)) -
        ∑ m ∈ Finset.range 2, ((-(a : ℂ)) ^ m / (m.factorial : ℂ)) := by
  simp [Finset.sum_range_succ]
  ring

lemma norm_exp_neg_sub_one_sub_le {a : ℝ} (ha : 0 ≤ a) :
    ‖Complex.exp (-(a : ℂ)) - (1 - (a : ℂ))‖ ≤ a ^ 2 * Real.exp a := by
  by_cases ha1 : a ≤ 1
  · have hx : ‖-(a : ℂ)‖ ≤ 1 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg ha] using ha1
    have h := Complex.exp_bound (x := -(a : ℂ)) (n := 2) hx (by norm_num)
    rw [← exp_neg_sub_linear_eq_taylor] at h
    norm_num [Real.norm_eq_abs, abs_of_nonneg ha] at h ⊢
    calc
      ‖Complex.exp (-(a : ℂ)) - (1 - (a : ℂ))‖ ≤ a ^ 2 * (3 / 4) := h
      _ ≤ a ^ 2 * Real.exp a := by
        gcongr
        exact (by norm_num : (3 / 4 : ℝ) ≤ 1).trans (Real.one_le_exp ha)
  · have ha_ge_one : 1 ≤ a := le_of_not_ge ha1
    have hexp_norm : ‖Complex.exp (-(a : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha)
    have hlinear_norm : ‖1 - (a : ℂ)‖ = a - 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr ha_ge_one)]
      ring
    calc
      ‖Complex.exp (-(a : ℂ)) - (1 - (a : ℂ))‖
          ≤ ‖Complex.exp (-(a : ℂ))‖ + ‖1 - (a : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + (a - 1) := by
        exact add_le_add hexp_norm hlinear_norm.le
      _ = a := by ring
      _ ≤ a ^ 2 * Real.exp a := by
        calc
          a ≤ a ^ 2 := by nlinarith
          _ = a ^ 2 * 1 := by ring
          _ ≤ a ^ 2 * Real.exp a := by
            exact mul_le_mul_of_nonneg_left (Real.one_le_exp ha) (sq_nonneg a)

lemma norm_prod_sub_prod_le_sum { ι : Type* } (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : ‖f a‖ ≤ 1 := hf a (Finset.mem_insert_self a s)
      have hf_s : ∀ i ∈ s, ‖f i‖ ≤ 1 := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      have hg_s : ∀ i ∈ s, ‖g i‖ ≤ 1 := by
        intro i hi
        exact hg i (Finset.mem_insert_of_mem hi)
      have hprod_g : ‖∏ i ∈ s, g i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i hi ↦ norm_nonneg (g i)) hg_s
      have ih_bound :
          ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ :=
        ih hf_s hg_s
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      calc
        ‖f a * ∏ x ∈ s, f x - g a * ∏ x ∈ s, g x‖ =
            ‖f a * ((∏ x ∈ s, f x) - ∏ x ∈ s, g x) +
              (f a - g a) * ∏ x ∈ s, g x‖ := by
                congr 1
                ring
        _ ≤ ‖f a * ((∏ x ∈ s, f x) - ∏ x ∈ s, g x)‖ +
              ‖(f a - g a) * ∏ x ∈ s, g x‖ := norm_add_le _ _
        _ = ‖f a‖ * ‖(∏ x ∈ s, f x) - ∏ x ∈ s, g x‖ +
              ‖f a - g a‖ * ‖∏ x ∈ s, g x‖ := by
                rw [norm_mul, norm_mul]
        _ ≤ 1 * (∑ x ∈ s, ‖f x - g x‖) + ‖f a - g a‖ * 1 := by
              apply add_le_add
              · exact mul_le_mul hfa ih_bound (norm_nonneg _) zero_le_one
              · exact mul_le_mul_of_nonneg_left hprod_g (norm_nonneg _)
        _ = ‖f a - g a‖ + ∑ x ∈ s, ‖f x - g x‖ := by ring

end

end Thm148Product

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

namespace Thm148Weights

open Thm148Core

def tailIntegral (μ : ProbabilityMeasure ℝ) (threshold : ℝ) : ℝ :=
  ∫ x in {x : ℝ | threshold ≤ |x|}, x ^ 2 ∂(μ : Measure ℝ)

def weight (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) : ℝ :=
  S.arrayNotation.variance n i / S.sn n ^ 2

def tailAggregate (S : Setup) (ε : ℝ) (n : ℕ) : ℝ :=
  (∑ i : Fin (S.arrayNotation.rowLength n),
      tailIntegral (S.rowLaws n i) (ε * S.sn n)) /
    S.sn n ^ 2

def LindebergCondition (S : Setup) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (tailAggregate S ε) atTop (𝓝 0)

namespace Setup

theorem variance_nonneg (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) :
    0 ≤ S.arrayNotation.variance n i := by
  rw [S.row_variance n i]
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg x)

theorem weight_nonneg (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) :
    0 ≤ weight S n i := by
  exact div_nonneg (variance_nonneg S n i) (sq_nonneg (S.sn n))

theorem sum_weight_eq_one (S : Setup) (n : ℕ) :
    ∑ i : Fin (S.arrayNotation.rowLength n), weight S n i = 1 := by
  rw [show (∑ i : Fin (S.arrayNotation.rowLength n), weight S n i) =
      (∑ i : Fin (S.arrayNotation.rowLength n),
        S.arrayNotation.variance n i) / S.sn n ^ 2 by
        simp only [weight, Finset.sum_div]]
  rw [← S.arrayNotation.totalVariance_eq n,
    ← S.sn_sq_eq_totalVariance n]
  exact div_self (ne_of_gt (sq_pos_of_pos (S.sn_pos n)))

theorem tailIntegral_nonneg (S : Setup) (ε : ℝ) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) :
    0 ≤ tailIntegral (S.rowLaws n i) (ε * S.sn n) := by
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun x : ℝ => sq_nonneg x)

theorem tailAggregate_nonneg (S : Setup) (ε : ℝ) (n : ℕ) :
    0 ≤ tailAggregate S ε n := by
  refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) (sq_nonneg (S.sn n))
  exact tailIntegral_nonneg S ε n i

theorem weight_le_sq_add_tailAggregate (S : Setup) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) (i : Fin (S.arrayNotation.rowLength n)) :
    weight S n i ≤ ε ^ 2 + tailAggregate S ε n := by
  let μ : ProbabilityMeasure ℝ := S.rowLaws n i
  let c : ℝ := ε * S.sn n
  let A : Set ℝ := {x : ℝ | c ≤ |x|}
  have hc : 0 < c := mul_pos hε (S.sn_pos n)
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_Ici.preimage continuous_abs.measurable
  have hsq : Integrable (fun x : ℝ => x ^ 2) (μ : Measure ℝ) := by
    simpa [μ] using S.row_sq_integrable n i
  have hinner_le :
      (∫ x in Aᶜ, x ^ 2 ∂(μ : Measure ℝ)) ≤ c ^ 2 := by
    calc
      (∫ x in Aᶜ, x ^ 2 ∂(μ : Measure ℝ))
          ≤ ∫ _x in Aᶜ, c ^ 2 ∂(μ : Measure ℝ) := by
            refine setIntegral_mono_on hsq.integrableOn
              (integrable_const (α := ℝ) (μ := (μ : Measure ℝ))
                (c ^ 2)).integrableOn hA.compl ?_
            intro x hx
            have hxlt : |x| < c := by
              simpa [A] using hx
            have habs_sq : |x| ^ 2 ≤ c ^ 2 :=
              (sq_le_sq₀ (abs_nonneg x) hc.le).2 hxlt.le
            simpa only [sq_abs] using habs_sq
      _ = (μ : Measure ℝ).real Aᶜ * c ^ 2 := by
            rw [setIntegral_const, smul_eq_mul]
      _ ≤ c ^ 2 := by
            exact mul_le_of_le_one_left (sq_nonneg c) measureReal_le_one
  have hsplit :
      S.arrayNotation.variance n i =
        tailIntegral (S.rowLaws n i) (ε * S.sn n) +
          ∫ x in Aᶜ, x ^ 2 ∂(μ : Measure ℝ) := by
    rw [S.row_variance n i]
    simpa [tailIntegral, μ, c, A] using
      (integral_add_compl hA hsq).symm
  have htail_le_sum :
      tailIntegral (S.rowLaws n i) (ε * S.sn n) ≤
        ∑ j : Fin (S.arrayNotation.rowLength n),
          tailIntegral (S.rowLaws n j) (ε * S.sn n) := by
    exact Finset.single_le_sum
      (fun j _ => tailIntegral_nonneg S ε n j) (Finset.mem_univ i)
  have hvariance_le :
      S.arrayNotation.variance n i ≤
        (∑ j : Fin (S.arrayNotation.rowLength n),
          tailIntegral (S.rowLaws n j) (ε * S.sn n)) + c ^ 2 := by
    rw [hsplit]
    exact add_le_add htail_le_sum hinner_le
  have hdenom : 0 < S.sn n ^ 2 := sq_pos_of_pos (S.sn_pos n)
  rw [weight, tailAggregate]
  apply (div_le_iff₀ hdenom).2
  calc
    S.arrayNotation.variance n i
        ≤ (∑ j : Fin (S.arrayNotation.rowLength n),
            tailIntegral (S.rowLaws n j) (ε * S.sn n)) + c ^ 2 :=
      hvariance_le
    _ = (ε ^ 2 +
          (∑ j : Fin (S.arrayNotation.rowLength n),
            tailIntegral (S.rowLaws n j) (ε * S.sn n)) /
              S.sn n ^ 2) * S.sn n ^ 2 := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hdenom)]
      dsimp [c]
      ring

def weightSquareSum (S : Setup) (n : ℕ) : ℝ :=
  ∑ i : Fin (S.arrayNotation.rowLength n), (weight S n i) ^ 2

theorem weightSquareSum_nonneg (S : Setup) (n : ℕ) :
    0 ≤ weightSquareSum S n := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (weight S n i)

theorem weightSquareSum_le_sq_add_tailAggregate
    (S : Setup) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    weightSquareSum S n ≤ ε ^ 2 + tailAggregate S ε n := by
  calc
    weightSquareSum S n
        = ∑ i : Fin (S.arrayNotation.rowLength n),
            weight S n i * weight S n i := by
              simp only [weightSquareSum, pow_two]
    _ ≤ ∑ i : Fin (S.arrayNotation.rowLength n),
          weight S n i * (ε ^ 2 + tailAggregate S ε n) := by
            exact Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left
                (weight_le_sq_add_tailAggregate S hε n i)
                (weight_nonneg S n i)
    _ = (∑ i : Fin (S.arrayNotation.rowLength n), weight S n i) *
          (ε ^ 2 + tailAggregate S ε n) := by
            rw [Finset.sum_mul]
    _ = ε ^ 2 + tailAggregate S ε n := by
            rw [sum_weight_eq_one S n, one_mul]

theorem tendsto_weightSquareSum_zero_of_lindeberg
    (S : Setup) (hL : LindebergCondition S) :
    Tendsto (weightSquareSum S) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro eps heps
  let ε : ℝ := Real.sqrt (eps / 2)
  have hhalf : 0 < eps / 2 := by linarith
  have hε : 0 < ε := Real.sqrt_pos.2 hhalf
  have hεsq : ε ^ 2 = eps / 2 := by
    exact Real.sq_sqrt hhalf.le
  rcases Metric.tendsto_atTop.mp (hL ε hε) (eps / 2) hhalf with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have htail_dist : dist (tailAggregate S ε n) 0 < eps / 2 := hN n hn
  have htail_lt : tailAggregate S ε n < eps / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg (tailAggregate_nonneg S ε n)] using
      htail_dist
  have hsum_lt : weightSquareSum S n < eps := by
    calc
      weightSquareSum S n ≤ ε ^ 2 + tailAggregate S ε n :=
        weightSquareSum_le_sq_add_tailAggregate S hε n
      _ < eps := by rw [hεsq]; linarith
  simpa [Real.dist_eq, abs_of_nonneg (weightSquareSum_nonneg S n)] using hsum_lt

end Setup

end Thm148Weights

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace Thm148ProductAssembly

open Thm148Core Thm148Core.Setup
open Thm148Product
open Thm148Weights

def quadraticWeight (S : Setup) (n : Nat)
    (i : Fin (S.arrayNotation.rowLength n)) (t : Real) : Real :=
  (t ^ 2 / 2) * weight S n i

lemma weight_le_one (S : Setup) (n : Nat)
    (i : Fin (S.arrayNotation.rowLength n)) : weight S n i <= 1 := by
  rw [← Thm148Weights.Setup.sum_weight_eq_one S n]
  exact Finset.single_le_sum
    (fun j _ => Thm148Weights.Setup.weight_nonneg S n j)
    (Finset.mem_univ i)

lemma quadraticWeight_nonneg (S : Setup) (n : Nat)
    (i : Fin (S.arrayNotation.rowLength n)) (t : Real) :
    0 <= quadraticWeight S n i t := by
  exact mul_nonneg (div_nonneg (sq_nonneg t) (by norm_num))
    (Thm148Weights.Setup.weight_nonneg S n i)

lemma quadraticWeight_le (S : Setup) (n : Nat)
    (i : Fin (S.arrayNotation.rowLength n)) (t : Real) :
    quadraticWeight S n i t <= t ^ 2 / 2 := by
  exact mul_le_of_le_one_right
    (div_nonneg (sq_nonneg t) (by norm_num)) (weight_le_one S n i)

lemma sum_quadraticWeight (S : Setup) (n : Nat) (t : Real) :
    (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
      quadraticWeight S n i t) = t ^ 2 / 2 := by
  simp only [quadraticWeight, ← Finset.mul_sum,
    Thm148Weights.Setup.sum_weight_eq_one, mul_one]

def quadraticErrorConstant (t : Real) : Real :=
  (t ^ 2 / 2) ^ 2 * Real.exp (t ^ 2 / 2)

lemma quadratic_exp_error_le_weight_sq (S : Setup) (n : Nat)
    (i : Fin (S.arrayNotation.rowLength n)) (t : Real) :
    (quadraticWeight S n i t) ^ 2 * Real.exp (quadraticWeight S n i t) <=
      quadraticErrorConstant t * (weight S n i) ^ 2 := by
  have ha : 0 <= quadraticWeight S n i t := quadraticWeight_nonneg S n i t
  have htop : quadraticWeight S n i t <= t ^ 2 / 2 :=
    quadraticWeight_le S n i t
  calc
    (quadraticWeight S n i t) ^ 2 * Real.exp (quadraticWeight S n i t)
        <= (quadraticWeight S n i t) ^ 2 * Real.exp (t ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htop)
            (sq_nonneg _)
    _ = quadraticErrorConstant t * (weight S n i) ^ 2 := by
          unfold quadraticWeight quadraticErrorConstant
          ring

def charFactor (S : Setup) (n : Nat)
    (i : Fin (S.arrayNotation.rowLength n)) (t : Real) : Complex :=
  charFun (S.rowLaws n i : Measure Real) (t / S.sn n)

def gaussianFactor (S : Setup) (n : Nat)
    (i : Fin (S.arrayNotation.rowLength n)) (t : Real) : Complex :=
  Complex.exp (-(quadraticWeight S n i t : Complex))

lemma norm_charFactor_le_one (S : Setup) (n : Nat)
    (i : Fin (S.arrayNotation.rowLength n)) (t : Real) :
    norm (charFactor S n i t) <= 1 := by
  exact MeasureTheory.norm_charFun_le_one _

lemma norm_gaussianFactor_le_one (S : Setup) (n : Nat)
    (i : Fin (S.arrayNotation.rowLength n)) (t : Real) :
    norm (gaussianFactor S n i t) <= 1 := by
  rw [gaussianFactor, Complex.norm_exp]
  exact Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (quadraticWeight_nonneg S n i t))

lemma norm_factor_sub_gaussian_le
    (S : Setup) (remainder : (n : Nat) ->
      Fin (S.arrayNotation.rowLength n) -> Real -> Complex)
    (hfactor : forall n i t,
      charFactor S n i t =
        1 - (quadraticWeight S n i t : Complex) + remainder n i t)
    (n : Nat) (i : Fin (S.arrayNotation.rowLength n)) (t : Real) :
    norm (charFactor S n i t - gaussianFactor S n i t) <=
      norm (remainder n i t) +
        quadraticErrorConstant t * (weight S n i) ^ 2 := by
  have ha : 0 <= quadraticWeight S n i t := quadraticWeight_nonneg S n i t
  have hexp := norm_exp_neg_sub_one_sub_le ha
  have hreverse :
      norm ((1 : Complex) - (quadraticWeight S n i t : Complex) -
        Complex.exp (-(quadraticWeight S n i t : Complex))) <=
        (quadraticWeight S n i t) ^ 2 *
          Real.exp (quadraticWeight S n i t) := by
    simpa [norm_sub_rev] using hexp
  rw [hfactor n i t]
  unfold gaussianFactor
  calc
    norm ((1 : Complex) - (quadraticWeight S n i t : Complex) +
        remainder n i t -
          Complex.exp (-(quadraticWeight S n i t : Complex))) =
      norm (remainder n i t +
        ((1 : Complex) - (quadraticWeight S n i t : Complex) -
          Complex.exp (-(quadraticWeight S n i t : Complex)))) := by
        congr 1
        ring
    _ <= norm (remainder n i t) +
        norm ((1 : Complex) - (quadraticWeight S n i t : Complex) -
          Complex.exp (-(quadraticWeight S n i t : Complex))) := norm_add_le _ _
    _ <= norm (remainder n i t) +
        (quadraticWeight S n i t) ^ 2 *
          Real.exp (quadraticWeight S n i t) := add_le_add le_rfl hreverse
    _ <= norm (remainder n i t) +
        quadraticErrorConstant t * (weight S n i) ^ 2 :=
      add_le_add le_rfl (quadratic_exp_error_le_weight_sq S n i t)

lemma gaussianProduct_eq (S : Setup) (n : Nat) (t : Real) :
    (Finset.univ.prod fun i : Fin (S.arrayNotation.rowLength n) =>
      gaussianFactor S n i t) =
        Complex.exp (-(t ^ 2 / 2 : Real)) := by
  calc
    (Finset.univ.prod fun i : Fin (S.arrayNotation.rowLength n) =>
      gaussianFactor S n i t) =
        Complex.exp (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
          -(quadraticWeight S n i t : Complex)) := by
            exact (Complex.exp_sum Finset.univ
              (fun i : Fin (S.arrayNotation.rowLength n) =>
                -(quadraticWeight S n i t : Complex))).symm
    _ = Complex.exp (-(t ^ 2 / 2 : Real)) := by
      congr 1
      rw [Finset.sum_neg_distrib]
      norm_cast
      exact congrArg Neg.neg (sum_quadraticWeight S n t)

theorem tendsto_charProduct_of_remainder_and_weights
    (S : Setup) (remainder : (n : Nat) ->
      Fin (S.arrayNotation.rowLength n) -> Real -> Complex)
    (hfactor : forall n i t,
      charFactor S n i t =
        1 - (quadraticWeight S n i t : Complex) + remainder n i t)
    (hrem : forall t : Real,
      Tendsto
        (fun n : Nat => Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
          norm (remainder n i t)) atTop (nhds 0))
    (hw : Tendsto (Thm148Weights.Setup.weightSquareSum S) atTop (nhds 0))
    (t : Real) :
    Tendsto
      (fun n : Nat => Finset.univ.prod fun i : Fin (S.arrayNotation.rowLength n) =>
        charFactor S n i t)
      atTop (nhds (Complex.exp (-(t ^ 2 / 2 : Real)))) := by
  let factorError : Nat -> Real := fun n =>
    Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
      norm (charFactor S n i t - gaussianFactor S n i t)
  let upper : Nat -> Real := fun n =>
    (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
      norm (remainder n i t)) +
        quadraticErrorConstant t * Thm148Weights.Setup.weightSquareSum S n
  have hupper : Tendsto upper atTop (nhds 0) := by
    simpa [upper] using
      (hrem t).add (Tendsto.const_mul (quadraticErrorConstant t) hw)
  have hfactorError : Tendsto factorError atTop (nhds 0) := by
    apply squeeze_zero' (g := upper)
    · exact Filter.Eventually.of_forall fun n =>
        Finset.sum_nonneg fun i _ => norm_nonneg _
    · exact Filter.Eventually.of_forall fun n => by
        unfold factorError upper Thm148Weights.Setup.weightSquareSum
        calc
          (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
            norm (charFactor S n i t - gaussianFactor S n i t)) <=
              Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
                (norm (remainder n i t) +
                  quadraticErrorConstant t * (weight S n i) ^ 2) := by
                    exact Finset.sum_le_sum fun i _ =>
                      norm_factor_sub_gaussian_le S remainder hfactor n i t
          _ = (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
                norm (remainder n i t)) +
              quadraticErrorConstant t *
                (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
                  (weight S n i) ^ 2) := by
                    rw [Finset.sum_add_distrib, Finset.mul_sum]
    · exact hupper
  have hprodNorm : Tendsto
      (fun n : Nat => norm
        ((Finset.univ.prod fun i : Fin (S.arrayNotation.rowLength n) =>
          charFactor S n i t) -
        (Finset.univ.prod fun i : Fin (S.arrayNotation.rowLength n) =>
          gaussianFactor S n i t))) atTop (nhds 0) := by
    apply squeeze_zero' (g := factorError)
    · exact Filter.Eventually.of_forall fun n => norm_nonneg _
    · exact Filter.Eventually.of_forall fun n => by
        unfold factorError
        simpa using norm_prod_sub_prod_le_sum
          (Finset.univ : Finset (Fin (S.arrayNotation.rowLength n)))
          (fun i => charFactor S n i t) (fun i => gaussianFactor S n i t)
          (fun i _ => norm_charFactor_le_one S n i t)
          (fun i _ => norm_gaussianFactor_le_one S n i t)
    · exact hfactorError
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [gaussianProduct_eq S] using hprodNorm

end Thm148ProductAssembly

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

namespace Thm148Lindeberg

open Thm148Product
open Thm148Core

def tailIntegral (μ : ProbabilityMeasure ℝ) (threshold : ℝ) : ℝ :=
  ∫ x in {x : ℝ | threshold ≤ |x|}, x ^ 2 ∂(μ : Measure ℝ)

def weight (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) : ℝ :=
  S.arrayNotation.variance n i / S.sn n ^ 2

def tailAggregate (S : Setup) (ε : ℝ) (n : ℕ) : ℝ :=
  (∑ i : Fin (S.arrayNotation.rowLength n),
      tailIntegral (S.rowLaws n i) (ε * S.sn n)) / S.sn n ^ 2

def LindebergCondition (S : Setup) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (tailAggregate S ε) atTop (𝓝 0)

lemma variance_nonneg (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) :
    0 ≤ S.arrayNotation.variance n i := by
  rw [S.row_variance n i]
  exact integral_nonneg_of_ae (ae_of_all _ fun x : ℝ ↦ sq_nonneg x)

lemma weight_nonneg (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) : 0 ≤ weight S n i :=
  div_nonneg (variance_nonneg S n i) (sq_nonneg (S.sn n))

lemma sum_weight_eq_one (S : Setup) (n : ℕ) :
    ∑ i : Fin (S.arrayNotation.rowLength n), weight S n i = 1 := by
  rw [show (∑ i : Fin (S.arrayNotation.rowLength n), weight S n i) =
      (∑ i : Fin (S.arrayNotation.rowLength n), S.arrayNotation.variance n i) /
        S.sn n ^ 2 by simp only [weight, Finset.sum_div]]
  rw [← S.arrayNotation.totalVariance_eq n, ← S.sn_sq_eq_totalVariance n]
  exact div_self (ne_of_gt (sq_pos_of_pos (S.sn_pos n)))

lemma tailIntegral_nonneg (S : Setup) (ε : ℝ) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) :
    0 ≤ tailIntegral (S.rowLaws n i) (ε * S.sn n) := by
  exact integral_nonneg_of_ae (ae_of_all _ fun x : ℝ ↦ sq_nonneg x)

lemma tailAggregate_nonneg (S : Setup) (ε : ℝ) (n : ℕ) :
    0 ≤ tailAggregate S ε n := by
  exact div_nonneg (Finset.sum_nonneg fun i _ ↦ tailIntegral_nonneg S ε n i)
    (sq_nonneg (S.sn n))

lemma norm_q_le_two_add_two_abs_add_sq (u : ℝ) :
    ‖q u‖ ≤ 2 + 2 * |u| + u ^ 2 / 2 := by
  unfold q
  calc
    ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I +
        (u : ℂ) ^ 2 / 2‖
        ≤ ‖Complex.exp ((u : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ +
            ‖(u : ℂ) * Complex.I‖ + ‖(u : ℂ) ^ 2 / 2‖ := by
          calc
            ‖Complex.exp ((u : ℂ) * Complex.I) - 1 - (u : ℂ) * Complex.I +
                (u : ℂ) ^ 2 / 2‖
                ≤ ‖Complex.exp ((u : ℂ) * Complex.I) - 1 -
                    (u : ℂ) * Complex.I‖ + ‖(u : ℂ) ^ 2 / 2‖ :=
                  norm_add_le _ _
            _ ≤ (‖Complex.exp ((u : ℂ) * Complex.I) - 1‖ +
                    ‖(u : ℂ) * Complex.I‖) + ‖(u : ℂ) ^ 2 / 2‖ := by
                  gcongr
                  exact norm_sub_le _ _
            _ ≤ (‖Complex.exp ((u : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ +
                    ‖(u : ℂ) * Complex.I‖) + ‖(u : ℂ) ^ 2 / 2‖ := by
                  gcongr
                  exact norm_sub_le _ _
    _ = 2 + |u| + u ^ 2 / 2 := by
      rw [Complex.norm_exp]
      simp [Real.norm_eq_abs]
      ring
    _ ≤ 2 + 2 * |u| + u ^ 2 / 2 := by linarith [abs_nonneg u]

lemma norm_q_le_tail_const_mul_sq {u c : ℝ} (hc : 0 < c) (hu : c ≤ |u|) :
    ‖q u‖ ≤ (2 / c ^ 2 + 2 / c + 1 / 2) * u ^ 2 := by
  have huabs : 0 < |u| := lt_of_lt_of_le hc hu
  have hu_sq : c ^ 2 ≤ u ^ 2 := by
    nlinarith [sq_nonneg (|u| - c), sq_abs u]
  have hone : 2 ≤ (2 / c ^ 2) * u ^ 2 := by
    calc
      2 = (2 / c ^ 2) * c ^ 2 := by field_simp [ne_of_gt hc]
      _ ≤ (2 / c ^ 2) * u ^ 2 :=
        mul_le_mul_of_nonneg_left hu_sq (by positivity)
  have hlinear : 2 * |u| ≤ (2 / c) * u ^ 2 := by
    have : c * |u| ≤ u ^ 2 := by
      nlinarith [mul_nonneg (abs_nonneg u) (sub_nonneg.mpr hu), sq_abs u]
    calc
      2 * |u| = (2 / c) * (c * |u|) := by field_simp [ne_of_gt hc]
      _ ≤ (2 / c) * u ^ 2 :=
        mul_le_mul_of_nonneg_left this (by positivity)
  calc
    ‖q u‖ ≤ 2 + 2 * |u| + u ^ 2 / 2 := norm_q_le_two_add_two_abs_add_sq u
    _ ≤ (2 / c ^ 2) * u ^ 2 + (2 / c) * u ^ 2 + (1 / 2) * u ^ 2 := by
      exact add_le_add (add_le_add hone hlinear) (le_of_eq (by ring))
    _ = (2 / c ^ 2 + 2 / c + 1 / 2) * u ^ 2 := by ring

lemma integrable_id_of_integrable_sq {μ : Measure ℝ}
    [IsFiniteMeasure μ] (hSq : Integrable (fun x : ℝ ↦ x ^ 2) μ) :
    Integrable (fun x : ℝ ↦ x) μ := by
  have hL2 : MemLp (fun x : ℝ ↦ x) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hSq
  exact hL2.integrable (by norm_num)

lemma continuous_q : Continuous q := by
  unfold q
  fun_prop

lemma integrable_q_mul {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hSq : Integrable (fun x : ℝ ↦ x ^ 2) μ) (u : ℝ) :
    Integrable (fun x : ℝ ↦ q (u * x)) μ := by
  have hId : Integrable (fun x : ℝ ↦ x) μ := integrable_id_of_integrable_sq hSq
  have hAbs : Integrable (fun x : ℝ ↦ |u * x|) μ := by
    simpa [abs_mul] using hId.abs.const_mul |u|
  have hSqScaled : Integrable (fun x : ℝ ↦ (u * x) ^ 2) μ := by
    have := hSq.const_mul (u ^ 2)
    simpa [mul_pow] using this
  have hDom : Integrable
      (fun x : ℝ ↦ 2 + 2 * |u * x| + (u * x) ^ 2 / 2) μ := by
    exact ((integrable_const (2 : ℝ)).add (hAbs.const_mul 2)).add
      (hSqScaled.div_const 2)
  refine Integrable.mono' hDom
    ((continuous_q.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  filter_upwards with x
  exact norm_q_le_two_add_two_abs_add_sq (u * x)

lemma charFun_eq_one_sub_variance_add_remainder
    (μ : ProbabilityMeasure ℝ) (u variance : ℝ)
    (hSq : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ))
    (hMean : ∫ x : ℝ, x ∂(μ : Measure ℝ) = 0)
    (hVariance : variance = ∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) :
    MeasureTheory.charFun (μ : Measure ℝ) u =
      1 - ((u : ℂ) ^ 2 * variance) / 2 +
        ∫ x : ℝ, q (u * x) ∂(μ : Measure ℝ) := by
  let ν : Measure ℝ := (μ : Measure ℝ)
  have hId : Integrable (fun x : ℝ ↦ x) ν :=
    integrable_id_of_integrable_sq hSq
  have hQ : Integrable (fun x : ℝ ↦ q (u * x)) ν :=
    integrable_q_mul hSq u
  have hLin : Integrable (fun x : ℝ ↦ ((u * x : ℝ) : ℂ) * Complex.I) ν := by
    have hC : Integrable (fun x : ℝ ↦ (x : ℂ)) ν := hId.ofReal
    simpa [Complex.ofReal_mul, mul_assoc] using
      (hC.const_mul (u : ℂ)).mul_const Complex.I
  have hQuad : Integrable (fun x : ℝ ↦ (((u * x : ℝ) : ℂ) ^ 2 / 2)) ν := by
    have hC : Integrable (fun x : ℝ ↦ ((x ^ 2 : ℝ) : ℂ)) ν := hSq.ofReal
    have hScaled := (hC.const_mul ((u : ℂ) ^ 2)).div_const (2 : ℂ)
    simpa [Complex.ofReal_mul, Complex.ofReal_pow, mul_pow, mul_assoc] using hScaled
  have hExp : Integrable
      (fun x : ℝ ↦ Complex.exp (((u * x : ℝ) : ℂ) * Complex.I)) ν := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
    filter_upwards with x
    rw [Complex.norm_exp]
    simp
  have hPoint : ∀ x : ℝ,
      Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I) =
        1 + ((u * x : ℝ) : ℂ) * Complex.I -
          (((u * x : ℝ) : ℂ) ^ 2 / 2) + q (u * x) := by
    intro x
    unfold q
    simp only [Complex.ofReal_mul]
    ring
  have hLinInt :
      (∫ x : ℝ, ((u * x : ℝ) : ℂ) * Complex.I ∂(μ : Measure ℝ)) = 0 := by
    rw [integral_mul_const]
    simp_rw [Complex.ofReal_mul]
    rw [integral_const_mul, integral_complex_ofReal, hMean]
    simp
  have hQuadInt :
      (∫ x : ℝ, (((u * x : ℝ) : ℂ) ^ 2 / 2) ∂(μ : Measure ℝ)) =
        ((u : ℂ) ^ 2 * variance) / 2 := by
    rw [integral_div]
    simp_rw [Complex.ofReal_mul, mul_pow]
    simp_rw [← Complex.ofReal_pow]
    rw [integral_const_mul, integral_complex_ofReal, ← hVariance]
  rw [MeasureTheory.charFun_apply_real]
  rw [integral_congr_ae (ae_of_all _ hPoint)]
  rw [integral_add]
  · rw [integral_sub]
    · rw [integral_add]
      · rw [integral_const, measureReal_def, measure_univ,
          ENNReal.toReal_one, one_smul]
        rw [hLinInt, hQuadInt]
        ring
      · exact integrable_const (1 : ℂ)
      · exact hLin
    · exact (integrable_const (1 : ℂ)).add hLin
    · exact hQuad
  · exact ((integrable_const (1 : ℂ)).add hLin).sub hQuad
  · exact hQ

lemma abs_scaled_mul_pow_three_le
    {t x s η : ℝ} (hs : 0 < s) (hx : |x| ≤ η * s) :
    |(t / s) * x| ^ 3 ≤ |t| ^ 3 * η * x ^ 2 / s ^ 2 := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  rw [abs_mul, abs_div, abs_of_pos hs]
  calc
    (|t| / s * |x|) ^ 3 = (|t| / s) ^ 3 * |x| ^ 2 * |x| := by ring
    _ ≤ (|t| / s) ^ 3 * |x| ^ 2 * (η * s) := by
      gcongr
    _ = |t| ^ 3 * η * x ^ 2 / s ^ 2 := by
      rw [sq_abs]
      field_simp [hs0]

lemma scaled_mul_sq (t x s : ℝ) :
    ((t / s) * x) ^ 2 = t ^ 2 * x ^ 2 / s ^ 2 := by ring

def cellRemainder (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) (t : ℝ) : ℂ :=
  ∫ x : ℝ, q ((t / S.sn n) * x) ∂(S.rowLaws n i : Measure ℝ)

lemma cellCharacteristic_eq (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) (t : ℝ) :
    MeasureTheory.charFun (S.rowLaws n i : Measure ℝ) (t / S.sn n) =
      1 - ((t : ℂ) ^ 2 * weight S n i) / 2 + cellRemainder S n i t := by
  have h := charFun_eq_one_sub_variance_add_remainder
    (S.rowLaws n i) (t / S.sn n) (S.arrayNotation.variance n i)
    (S.row_sq_integrable n i) (S.row_mean_zero n i) (S.row_variance n i)
  rw [h]
  unfold cellRemainder weight
  congr 1
  push_cast
  have hs0 : S.sn n ≠ 0 := ne_of_gt (S.sn_pos n)
  field_simp [hs0]

lemma norm_cellRemainder_le (S : Setup) (n : ℕ)
    (i : Fin (S.arrayNotation.rowLength n)) {t η : ℝ}
    (ht : t ≠ 0) (hη : 0 < η) (htη : |t| * η ≤ 1) :
    ‖cellRemainder S n i t‖ ≤
      (|t| ^ 3 * η) * weight S n i +
        ((2 / (|t| * η) ^ 2 + 2 / (|t| * η) + 1 / 2) * t ^ 2) *
          tailIntegral (S.rowLaws n i) (η * S.sn n) / S.sn n ^ 2 := by
  let s := S.sn n
  let A := |t| ^ 3 * η
  let C := 2 / (|t| * η) ^ 2 + 2 / (|t| * η) + 1 / 2
  let B := C * t ^ 2
  let T : Set ℝ := {x : ℝ | η * s ≤ |x|}
  have hs : 0 < s := S.sn_pos n
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hc : 0 < |t| * η := mul_pos (abs_pos.mpr ht) hη
  have hA : 0 ≤ A := mul_nonneg (pow_nonneg (abs_nonneg t) 3) hη.le
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hB : 0 ≤ B := mul_nonneg hC (sq_nonneg t)
  have hSq := S.row_sq_integrable n i
  have hTailMeas : MeasurableSet T := by
    dsimp [T]
    exact measurableSet_Ici.preimage continuous_abs.measurable
  have hTailInt : Integrable (T.indicator (fun x : ℝ ↦ x ^ 2))
      (S.rowLaws n i : Measure ℝ) :=
    hSq.indicator hTailMeas
  have hDom : Integrable
      (fun x : ℝ ↦ A * x ^ 2 / s ^ 2 +
        B * T.indicator (fun y : ℝ ↦ y ^ 2) x / s ^ 2)
      (S.rowLaws n i : Measure ℝ) := by
    have h1 := (hSq.const_mul A).div_const (s ^ 2)
    have h2 := (hTailInt.const_mul B).div_const (s ^ 2)
    exact h1.add h2
  have hPoint : ∀ x : ℝ,
      ‖q ((t / s) * x)‖ ≤
        A * x ^ 2 / s ^ 2 + B * T.indicator (fun y : ℝ ↦ y ^ 2) x / s ^ 2 := by
    intro x
    by_cases hxT : x ∈ T
    · have hx : η * s ≤ |x| := hxT
      have hu : |t| * η ≤ |(t / s) * x| := by
        rw [abs_mul, abs_div, abs_of_pos hs]
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hs).2
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hx (abs_nonneg t)
      have hq := norm_q_le_tail_const_mul_sq hc hu
      rw [scaled_mul_sq] at hq
      rw [Set.indicator_of_mem hxT]
      calc
        ‖q ((t / s) * x)‖ ≤ C * (t ^ 2 * x ^ 2 / s ^ 2) := by
          simpa [C] using hq
        _ = B * x ^ 2 / s ^ 2 := by simp [B]; ring
        _ ≤ A * x ^ 2 / s ^ 2 + B * x ^ 2 / s ^ 2 := by
          have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
          have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
          have : 0 ≤ A * x ^ 2 / s ^ 2 := div_nonneg (mul_nonneg hA hx2) hs2
          linarith
    · have hx : |x| ≤ η * s := le_of_not_ge hxT
      have hu : |(t / s) * x| ≤ 1 := by
        calc
          |(t / s) * x| ≤ |t| * η := by
            rw [abs_mul, abs_div, abs_of_pos hs]
            rw [div_mul_eq_mul_div]
            apply (div_le_iff₀ hs).2
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hx (abs_nonneg t)
          _ ≤ 1 := htη
      have hq := norm_q_le_abs_pow_three hu
      simp only [Set.indicator, hxT, if_false, mul_zero, zero_div, add_zero]
      exact hq.trans (abs_scaled_mul_pow_three_le hs hx)
  have hNorm :
      ‖cellRemainder S n i t‖ ≤
        ∫ x : ℝ, (A * x ^ 2 / s ^ 2 +
          B * T.indicator (fun y : ℝ ↦ y ^ 2) x / s ^ 2)
          ∂(S.rowLaws n i : Measure ℝ) := by
    unfold cellRemainder
    exact norm_integral_le_of_norm_le hDom (ae_of_all _ hPoint)
  calc
    ‖cellRemainder S n i t‖ ≤
        ∫ x : ℝ, (A * x ^ 2 / s ^ 2 +
          B * T.indicator (fun y : ℝ ↦ y ^ 2) x / s ^ 2)
          ∂(S.rowLaws n i : Measure ℝ) := hNorm
    _ = A * weight S n i +
        B * tailIntegral (S.rowLaws n i) (η * S.sn n) / S.sn n ^ 2 := by
      rw [integral_add]
      · rw [integral_div, integral_const_mul, integral_div, integral_const_mul]
        rw [show ∫ x : ℝ, T.indicator (fun y : ℝ ↦ y ^ 2) x
              ∂(S.rowLaws n i : Measure ℝ) =
            tailIntegral (S.rowLaws n i) (η * S.sn n) by
              rw [integral_indicator hTailMeas]
              rfl]
        rw [← S.row_variance n i]
        simp only [A, B, s]
        unfold weight
        ring
      · exact (hSq.const_mul A).div_const (s ^ 2)
      · exact (hTailInt.const_mul B).div_const (s ^ 2)
    _ = (|t| ^ 3 * η) * weight S n i +
        ((2 / (|t| * η) ^ 2 + 2 / (|t| * η) + 1 / 2) * t ^ 2) *
          tailIntegral (S.rowLaws n i) (η * S.sn n) / S.sn n ^ 2 := by
      rfl

lemma sum_norm_cellRemainder_le (S : Setup) (n : ℕ) {t η : ℝ}
    (ht : t ≠ 0) (hη : 0 < η) (htη : |t| * η ≤ 1) :
    (∑ i : Fin (S.arrayNotation.rowLength n), ‖cellRemainder S n i t‖) ≤
      |t| ^ 3 * η +
        ((2 / (|t| * η) ^ 2 + 2 / (|t| * η) + 1 / 2) * t ^ 2) *
          tailAggregate S η n := by
  let B := (2 / (|t| * η) ^ 2 + 2 / (|t| * η) + 1 / 2) * t ^ 2
  calc
    (∑ i : Fin (S.arrayNotation.rowLength n), ‖cellRemainder S n i t‖)
        ≤ ∑ i : Fin (S.arrayNotation.rowLength n),
            ((|t| ^ 3 * η) * weight S n i +
              B * tailIntegral (S.rowLaws n i) (η * S.sn n) / S.sn n ^ 2) := by
          exact Finset.sum_le_sum fun i _ ↦ by
            simpa [B] using norm_cellRemainder_le S n i ht hη htη
    _ = (|t| ^ 3 * η) *
          (∑ i : Fin (S.arrayNotation.rowLength n), weight S n i) +
        B * ((∑ i : Fin (S.arrayNotation.rowLength n),
          tailIntegral (S.rowLaws n i) (η * S.sn n)) / S.sn n ^ 2) := by
          rw [Finset.sum_add_distrib]
          rw [← Finset.mul_sum]
          rw [← Finset.sum_div]
          congr 1
          rw [← Finset.mul_sum]
          ring
    _ = |t| ^ 3 * η + B * tailAggregate S η n := by
          rw [sum_weight_eq_one S n]
          simp [tailAggregate]
    _ = |t| ^ 3 * η +
        ((2 / (|t| * η) ^ 2 + 2 / (|t| * η) + 1 / 2) * t ^ 2) *
          tailAggregate S η n := by rfl

def remainderNormSum (S : Setup) (t : ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin (S.arrayNotation.rowLength n), ‖cellRemainder S n i t‖

lemma remainderNormSum_nonneg (S : Setup) (t : ℝ) (n : ℕ) :
    0 ≤ remainderNormSum S t n :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

theorem tendsto_remainderNormSum_zero_of_lindeberg
    (S : Setup) (hL : LindebergCondition S) (t : ℝ) :
    Tendsto (remainderNormSum S t) atTop (𝓝 0) := by
  by_cases ht : t = 0
  · subst t
    have hzero : remainderNormSum S 0 = fun _ : ℕ ↦ 0 := by
      funext n
      simp [remainderNormSum, cellRemainder, q]
    rw [hzero]
    exact tendsto_const_nhds
  · have htAbs : 0 < |t| := abs_pos.mpr ht
    have htCube : 0 < |t| ^ 3 := pow_pos htAbs 3
    refine Metric.tendsto_atTop.2 ?_
    intro ρ hρ
    let η : ℝ := min (1 / (2 * |t|)) (ρ / (2 * |t| ^ 3))
    have hη : 0 < η := by
      dsimp [η]
      exact lt_min (one_div_pos.mpr (mul_pos zero_lt_two htAbs))
        (div_pos hρ (mul_pos zero_lt_two htCube))
    have hηLeft : η ≤ 1 / (2 * |t|) := min_le_left _ _
    have hηRight : η ≤ ρ / (2 * |t| ^ 3) := min_le_right _ _
    have htη : |t| * η ≤ 1 := by
      calc
        |t| * η ≤ |t| * (1 / (2 * |t|)) :=
          mul_le_mul_of_nonneg_left hηLeft (abs_nonneg t)
        _ = 1 / 2 := by field_simp [ne_of_gt htAbs]
        _ ≤ 1 := by norm_num
    have hSmall : |t| ^ 3 * η ≤ ρ / 2 := by
      calc
        |t| ^ 3 * η ≤ |t| ^ 3 * (ρ / (2 * |t| ^ 3)) :=
          mul_le_mul_of_nonneg_left hηRight (pow_nonneg (abs_nonneg t) 3)
        _ = ρ / 2 := by field_simp [ne_of_gt htCube]
    let B : ℝ :=
      (2 / (|t| * η) ^ 2 + 2 / (|t| * η) + 1 / 2) * t ^ 2
    have hB : 0 ≤ B := by
      dsimp [B]
      positivity
    have hBL : Tendsto (fun n : ℕ ↦ B * tailAggregate S η n)
        atTop (𝓝 0) := by
      simpa using (Filter.Tendsto.const_mul B (hL η hη))
    have hhalf : 0 < ρ / 2 := by linarith
    rcases Metric.tendsto_atTop.mp hBL (ρ / 2) hhalf with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hTailNonneg : 0 ≤ B * tailAggregate S η n :=
      mul_nonneg hB (tailAggregate_nonneg S η n)
    have hTail : B * tailAggregate S η n < ρ / 2 := by
      have hd := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hTailNonneg] at hd
      exact hd
    have hBound : remainderNormSum S t n ≤
        |t| ^ 3 * η + B * tailAggregate S η n := by
      simpa [remainderNormSum, B] using
        sum_norm_cellRemainder_le S n ht hη htη
    have hlt : remainderNormSum S t n < ρ :=
      lt_of_le_of_lt hBound (by linarith)
    simpa [Real.dist_eq, abs_of_nonneg (remainderNormSum_nonneg S t n)] using hlt

lemma weightsLindebergCondition_of (S : Setup) (hL : LindebergCondition S) :
    Thm148Weights.LindebergCondition S := by
  intro ε hε
  have heq : Thm148Weights.tailAggregate S ε = tailAggregate S ε := by
    funext n
    rfl
  rw [heq]
  exact hL ε hε

theorem tendsto_standardizedSum_charFun_of_lindeberg
    (S : Setup) (hL : LindebergCondition S) (t : ℝ) :
    Tendsto
      (fun n : ℕ ↦ MeasureTheory.charFun (S.standardizedSumLaw n : Measure ℝ) t)
      atTop
      (𝓝 (MeasureTheory.charFun
        (Thm148Core.Setup.standardNormalLaw : ProbabilityMeasure ℝ) t)) := by
  have hfactor : ∀ n i u,
      Thm148ProductAssembly.charFactor S n i u =
        1 - (Thm148ProductAssembly.quadraticWeight S n i u : ℂ) +
          cellRemainder S n i u := by
    intro n i u
    have h := cellCharacteristic_eq S n i u
    unfold Thm148ProductAssembly.charFactor
      Thm148ProductAssembly.quadraticWeight
      Thm148Weights.weight
    rw [h]
    unfold weight
    push_cast
    ring
  have hrem : ∀ u : ℝ,
      Tendsto
        (fun n : ℕ ↦ ∑ i : Fin (S.arrayNotation.rowLength n),
          ‖cellRemainder S n i u‖) atTop (𝓝 0) := by
    intro u
    change Tendsto (remainderNormSum S u) atTop (𝓝 0)
    exact tendsto_remainderNormSum_zero_of_lindeberg S hL u
  have hw : Tendsto
      (Thm148Weights.Setup.weightSquareSum S) atTop (𝓝 0) :=
    Thm148Weights.Setup.tendsto_weightSquareSum_zero_of_lindeberg S
      (weightsLindebergCondition_of S hL)
  have hprod :=
    Thm148ProductAssembly.tendsto_charProduct_of_remainder_and_weights
      S (cellRemainder S) hfactor hrem hw t
  have htarget :
      MeasureTheory.charFun
          (Thm148Core.Setup.standardNormalLaw : ProbabilityMeasure ℝ) t =
        Complex.exp (-(t ^ 2 / 2 : ℝ)) := by
    calc
      MeasureTheory.charFun
          (Thm148Core.Setup.standardNormalLaw : ProbabilityMeasure ℝ) t =
          Complex.exp (-((t : ℂ) ^ 2) / 2) := by
            simpa [Thm148Core.Setup.standardNormalLaw,
              thm_14_1_characteristicFunction,
              thm_14_7_standardNormalCharacteristic] using
              thm_14_7_standardNormalLaw_characteristic t
      _ = Complex.exp (-(t ^ 2 / 2 : ℝ)) := by
            congr 1
            push_cast
            ring
  rw [htarget]
  refine hprod.congr' ?_
  filter_upwards with n
  have hrow :=
    Thm148Core.Setup.standardizedSumCharacteristic_eq_prod S n t
  simpa [Thm148ProductAssembly.charFactor,
    thm_14_1_characteristicFunction] using hrow.symm

theorem lindeberg_triangularArray_clt
    (S : Setup) (hL : LindebergCondition S) :
    Tendsto S.standardizedSumLaw atTop
      (𝓝 Thm148Core.Setup.standardNormalLaw) := by
  refine (ProbabilityMeasure.tendsto_iff_tendsto_charFun).2 ?_
  intro t
  exact tendsto_standardizedSum_charFun_of_lindeberg S hL t

end Thm148Lindeberg

open MeasureTheory

noncomputable section

namespace Thm148Lyapunov

theorem sq_le_rpow_div_rpow_of_le_abs
    {c δ x : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hx : c ≤ |x|) :
    x ^ 2 ≤ Real.rpow |x| (2 + δ) / Real.rpow c δ := by
  have habs : 0 < |x| := lt_of_lt_of_le hc hx
  have hcδpos : 0 < Real.rpow c δ := Real.rpow_pos_of_pos hc δ
  have hpow : Real.rpow c δ ≤ Real.rpow |x| δ :=
    Real.rpow_le_rpow hc.le hx hδ.le
  apply (le_div_iff₀ hcδpos).2
  calc
    x ^ 2 * Real.rpow c δ
        ≤ x ^ 2 * Real.rpow |x| δ :=
          mul_le_mul_of_nonneg_left hpow (sq_nonneg x)
    _ = Real.rpow |x| 2 * Real.rpow |x| δ := by
          congr 1
          exact ((Real.rpow_two |x|).trans (sq_abs x)).symm
    _ = Real.rpow |x| (2 + δ) :=
          (Real.rpow_add habs 2 δ).symm

theorem setIntegral_sq_le_integral_rpow_div
    (μ : ProbabilityMeasure ℝ) {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (hmoment :
      Integrable (fun x : ℝ => Real.rpow |x| (2 + δ))
        (μ : Measure ℝ)) :
    (∫ x in {x : ℝ | c ≤ |x|}, x ^ 2 ∂(μ : Measure ℝ))
      ≤ (∫ x, Real.rpow |x| (2 + δ) ∂(μ : Measure ℝ)) /
          Real.rpow c δ := by
  let s : Set ℝ := {x : ℝ | c ≤ |x|}
  let g : ℝ → ℝ :=
    fun x => Real.rpow |x| (2 + δ) / Real.rpow c δ
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_Ici.preimage continuous_abs.measurable
  have hdenom_pos : 0 < Real.rpow c δ := Real.rpow_pos_of_pos hc δ
  have hg : Integrable g (μ : Measure ℝ) := by
    dsimp [g]
    exact hmoment.div_const (Real.rpow c δ)
  have hsq_on : IntegrableOn (fun x : ℝ => x ^ 2) s (μ : Measure ℝ) := by
    apply Integrable.mono' hg.integrableOn
    · fun_prop
    · filter_upwards [ae_restrict_mem hs] with x hx
      rw [Real.norm_eq_abs, abs_sq]
      exact sq_le_rpow_div_rpow_of_le_abs hc hδ hx
  calc
    (∫ x in {x : ℝ | c ≤ |x|}, x ^ 2 ∂(μ : Measure ℝ))
        = ∫ x in s, x ^ 2 ∂(μ : Measure ℝ) := by rfl
    _ ≤ ∫ x in s, g x ∂(μ : Measure ℝ) := by
          refine setIntegral_mono_on hsq_on hg.integrableOn hs ?_
          intro x hx
          exact sq_le_rpow_div_rpow_of_le_abs hc hδ hx
    _ ≤ ∫ x, g x ∂(μ : Measure ℝ) := by
          refine setIntegral_le_integral hg ?_
          filter_upwards with x
          exact div_nonneg (Real.rpow_nonneg (abs_nonneg x) (2 + δ))
            hdenom_pos.le
    _ = (∫ x, Real.rpow |x| (2 + δ) ∂(μ : Measure ℝ)) /
          Real.rpow c δ := by
          dsimp [g]
          exact integral_div (Real.rpow c δ)
            (fun x : ℝ => Real.rpow |x| (2 + δ))

theorem sum_setIntegral_sq_le_sum_integral_rpow_div
    {k : ℕ} (μ : Fin k → ProbabilityMeasure ℝ) {c δ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ)
    (hmoment : ∀ i : Fin k,
      Integrable (fun x : ℝ => Real.rpow |x| (2 + δ))
        (μ i : Measure ℝ)) :
    (∑ i : Fin k,
      ∫ x in {x : ℝ | c ≤ |x|}, x ^ 2 ∂(μ i : Measure ℝ))
      ≤ (∑ i : Fin k,
          ∫ x, Real.rpow |x| (2 + δ) ∂(μ i : Measure ℝ)) /
            Real.rpow c δ := by
  calc
    (∑ i : Fin k,
      ∫ x in {x : ℝ | c ≤ |x|}, x ^ 2 ∂(μ i : Measure ℝ))
        ≤ ∑ i : Fin k,
            (∫ x, Real.rpow |x| (2 + δ) ∂(μ i : Measure ℝ)) /
              Real.rpow c δ := by
          exact Finset.sum_le_sum fun i _ =>
            setIntegral_sq_le_integral_rpow_div (μ i) hc hδ (hmoment i)
    _ = (∑ i : Fin k,
          ∫ x, Real.rpow |x| (2 + δ) ∂(μ i : Measure ℝ)) /
            Real.rpow c δ := by
          rw [Finset.sum_div]

end Thm148Lyapunov

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

namespace Thm148LyapunovImplication

open Thm148Core Thm148Core.Setup
open Thm148Lyapunov

def tailIntegral (mu : ProbabilityMeasure Real) (threshold : Real) : Real :=
  ∫ x in {x : Real | threshold <= |x|}, x ^ 2 ∂(mu : Measure Real)

def lyapunovMoment (mu : ProbabilityMeasure Real) (delta : Real) : Real :=
  ∫ x, Real.rpow |x| (2 + delta) ∂(mu : Measure Real)

def LindebergCondition (S : Setup) : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    Tendsto
      (fun n : Nat =>
        (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
          tailIntegral (S.rowLaws n i) (epsilon * S.sn n)) /
            S.sn n ^ 2)
      atTop (nhds 0)

def LyapunovCondition (S : Setup) : Prop :=
  exists delta : Real, 0 < delta /\
    (forall n : Nat, forall i : Fin (S.arrayNotation.rowLength n),
      Integrable (fun x : Real => Real.rpow |x| (2 + delta))
        (S.rowLaws n i : Measure Real)) /\
    Tendsto
      (fun n : Nat =>
        (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
          lyapunovMoment (S.rowLaws n i) delta) /
            Real.rpow (S.sn n) (2 + delta))
      atTop (nhds 0)

lemma lyapunov_denominator_identity
    {epsilon s delta M : Real} (hepsilon : 0 < epsilon) (hs : 0 < s) :
    (M / Real.rpow (epsilon * s) delta) / s ^ 2 =
      (Real.rpow epsilon delta)⁻¹ *
        (M / Real.rpow s (2 + delta)) := by
  have he : 0 <= epsilon := hepsilon.le
  have hsn : 0 <= s := hs.le
  have hepow : Real.rpow epsilon delta ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hepsilon delta)
  have hspow : Real.rpow s delta ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hs delta)
  have hsne : s ≠ 0 := ne_of_gt hs
  change M / ((epsilon * s) ^ delta) / s ^ 2 =
    (epsilon ^ delta)⁻¹ * (M / s ^ (2 + delta))
  rw [Real.mul_rpow (z := delta) he hsn]
  rw [Real.rpow_add hs 2 delta, Real.rpow_two]
  field_simp

lemma tail_row_nonneg (S : Setup) (epsilon : Real) (n : Nat) :
    0 <=
      (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
        tailIntegral (S.rowLaws n i) (epsilon * S.sn n)) /
          S.sn n ^ 2 := by
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    unfold tailIntegral
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x : Real => sq_nonneg x)
  · exact sq_nonneg _

lemma lyapunov_tail_row_upper
    (S : Setup) {epsilon delta : Real}
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hmoment : forall n : Nat, forall i : Fin (S.arrayNotation.rowLength n),
      Integrable (fun x : Real => Real.rpow |x| (2 + delta))
        (S.rowLaws n i : Measure Real))
    (n : Nat) :
    (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
      tailIntegral (S.rowLaws n i) (epsilon * S.sn n)) /
        S.sn n ^ 2 <=
      (Real.rpow epsilon delta)⁻¹ *
        ((Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
          lyapunovMoment (S.rowLaws n i) delta) /
            Real.rpow (S.sn n) (2 + delta)) := by
  have hcut : 0 < epsilon * S.sn n := mul_pos hepsilon (S.sn_pos n)
  have hsum := sum_setIntegral_sq_le_sum_integral_rpow_div
    (S.rowLaws n) hcut hdelta (hmoment n)
  have hden : 0 <= S.sn n ^ 2 := sq_nonneg _
  have hdiv := div_le_div_of_nonneg_right hsum hden
  rw [lyapunov_denominator_identity hepsilon (S.sn_pos n)] at hdiv
  exact hdiv

theorem lyapunov_implies_lindeberg (S : Setup) :
    LyapunovCondition S -> LindebergCondition S := by
  rintro ⟨delta, hdelta, hmoment, hlimit⟩
  intro epsilon hepsilon
  let Y : Nat -> Real := fun n =>
    (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
      lyapunovMoment (S.rowLaws n i) delta) /
        Real.rpow (S.sn n) (2 + delta)
  let C : Real := (Real.rpow epsilon delta)⁻¹
  have hCY : Tendsto (fun n => C * Y n) atTop (nhds 0) := by
    simpa [C, Y] using (Tendsto.const_mul C hlimit)
  apply squeeze_zero' (g := fun n => C * Y n)
  · exact Filter.Eventually.of_forall (tail_row_nonneg S epsilon)
  · exact Filter.Eventually.of_forall fun n => by
      simpa [C, Y] using
        lyapunov_tail_row_upper S hepsilon hdelta hmoment n
  · exact hCY

end Thm148LyapunovImplication

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

abbrev thm_14_8_TriangularArrayNotation :=
  chapter14_TriangularArrayNotation

def thm_14_8_lindebergTailIntegral
    (mu : ProbabilityMeasure Real) (threshold : Real) : Real :=
  ∫ x in {x : Real | threshold <= |x|}, x ^ 2 ∂(mu : Measure Real)

def thm_14_8_lyapunovMoment
    (mu : ProbabilityMeasure Real) (delta : Real) : Real :=
  ∫ x, Real.rpow |x| (2 + delta) ∂(mu : Measure Real)

abbrev thm_14_8_TriangularArraySetup := Thm148Core.Setup

def thm_14_8_LindebergCondition
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    Tendsto
      (fun n : Nat =>
        (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
          thm_14_8_lindebergTailIntegral
            (S.rowLaws n i) (epsilon * S.sn n)) /
              S.sn n ^ 2)
      atTop (nhds 0)

def thm_14_8_LyapunovCondition
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  exists delta : Real, 0 < delta /\
    (forall n : Nat, forall i : Fin (S.arrayNotation.rowLength n),
      Integrable (fun x : Real => Real.rpow |x| (2 + delta))
        (S.rowLaws n i : Measure Real)) /\
    Tendsto
      (fun n : Nat =>
        (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
          thm_14_8_lyapunovMoment (S.rowLaws n i) delta) /
            Real.rpow (S.sn n) (2 + delta))
      atTop (nhds 0)

def thm_14_8_condition
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  thm_14_8_LindebergCondition S \/ thm_14_8_LyapunovCondition S

def thm_14_8_conclusion
    (S : thm_14_8_TriangularArraySetup) : Prop :=
  Tendsto S.standardizedSumLaw atTop
    (nhds Thm148Core.Setup.standardNormalLaw)

theorem thm_14_8_of_lindeberg
    (S : thm_14_8_TriangularArraySetup)
    (hL : thm_14_8_LindebergCondition S) :
    thm_14_8_conclusion S := by
  have hL' : Thm148Lindeberg.LindebergCondition S := by
    intro epsilon hepsilon
    change Tendsto
      (fun n : Nat =>
        (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
          ∫ x in {x : Real | epsilon * S.sn n <= |x|}, x ^ 2
            ∂(S.rowLaws n i : Measure Real)) / S.sn n ^ 2)
      atTop (nhds 0)
    exact hL epsilon hepsilon
  exact Thm148Lindeberg.lindeberg_triangularArray_clt S hL'

theorem thm_14_8_of_lyapunov
    (S : thm_14_8_TriangularArraySetup)
    (hY : thm_14_8_LyapunovCondition S) :
    thm_14_8_conclusion S := by
  have hY' : Thm148LyapunovImplication.LyapunovCondition S := by
    simpa [thm_14_8_LyapunovCondition,
      thm_14_8_lyapunovMoment,
      Thm148LyapunovImplication.LyapunovCondition,
      Thm148LyapunovImplication.lyapunovMoment] using hY
  have hLI : Thm148LyapunovImplication.LindebergCondition S :=
    Thm148LyapunovImplication.lyapunov_implies_lindeberg S hY'
  have hL : Thm148Lindeberg.LindebergCondition S := by
    intro epsilon hepsilon
    change Tendsto
      (fun n : Nat =>
        (Finset.univ.sum fun i : Fin (S.arrayNotation.rowLength n) =>
          ∫ x in {x : Real | epsilon * S.sn n <= |x|}, x ^ 2
            ∂(S.rowLaws n i : Measure Real)) / S.sn n ^ 2)
      atTop (nhds 0)
    exact hLI epsilon hepsilon
  exact Thm148Lindeberg.lindeberg_triangularArray_clt S hL

theorem thm_14_8
    (S : thm_14_8_TriangularArraySetup)
    (h : thm_14_8_condition S) :
    thm_14_8_conclusion S := by
  rcases h with hL | hY
  · exact thm_14_8_of_lindeberg S hL
  · exact thm_14_8_of_lyapunov S hY
