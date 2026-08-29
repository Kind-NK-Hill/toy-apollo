/-
TASK ID: thm_11_7_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_5_10
import ToyApollo.Output.def_9_1
import ToyApollo.Output.thm_5_8
import ToyApollo.Output.thm_10_1
import ToyApollo.Output.thm_11_1
import ToyApollo.Output.thm_11_5

open Filter
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

def thm_11_7_fourthMomentUniformBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (_μ c : ℝ) : Prop :=
  0 ≤ c ∧
    ∀ i : ℕ,
      MemLp (X i) 4 P ∧
        ∃ hXi : FiniteAbsMoment P (X i) 4,
          rthMoment P (X i) positiveOrderFour hXi ≤ c

def thm_11_7_centeredFourthMomentUniformBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ c : ℝ) : Prop :=
  0 ≤ c ∧
    ∀ i : ℕ,
      MemLp (fun ω => X i ω - μ) 4 P ∧
        ∃ hXi : FiniteAbsMoment P (fun ω => X i ω - μ) 4,
          rthMoment P (fun ω => X i ω - μ) positiveOrderFour hXi ≤ c

noncomputable def thm_11_7_centeredPartialSum {Ω : Type*} (X : ℕ → Ω → ℝ)
    (μ : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i : Fin (n + 1), (X i.1 ω - μ)

theorem thm_11_7_centeredPartialSum_fourth_expand {Ω : Type*}
    (X : ℕ → Ω → ℝ) (μ : ℝ) (n : ℕ) (ω : Ω) :
    (thm_11_7_centeredPartialSum X μ n ω) ^ 4 =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
        ∑ l : Fin (n + 1),
          (X i.1 ω - μ) * (X j.1 ω - μ) *
            (X k.1 ω - μ) * (X l.1 ω - μ) := by
  change (∑ i : Fin (n + 1), (X i.1 ω - μ)) ^ 4 =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
        ∑ l : Fin (n + 1),
          (X i.1 ω - μ) * (X j.1 ω - μ) *
            (X k.1 ω - μ) * (X l.1 ω - μ)
  rw [show (∑ i : Fin (n + 1), (X i.1 ω - μ)) ^ 4 =
      ((∑ i : Fin (n + 1), (X i.1 ω - μ)) *
          (∑ j : Fin (n + 1), (X j.1 ω - μ))) *
        ((∑ k : Fin (n + 1), (X k.1 ω - μ)) *
          (∑ l : Fin (n + 1), (X l.1 ω - μ))) by ring]
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  refine Finset.sum_congr rfl ?_
  intro j _hj
  refine Finset.sum_congr rfl ?_
  intro k _hk
  refine Finset.sum_congr rfl ?_
  intro l _hl
  ring

theorem thm_11_7_centered_independence {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hInd : def_5_10_randomVariables P X) :
    def_5_10_randomVariables P (fun i ω => X i ω - μ) := by
  dsimp [def_5_10_randomVariables] at hInd ⊢
  simpa [Function.comp_def] using
    hInd.comp (fun _ x => x - μ) (fun _ => measurable_id.sub measurable_const)

theorem thm_11_7_centered_pairwise_indepFun {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hInd : def_5_10_randomVariables P X) {i j : ℕ} (hij : i ≠ j) :
    ProbabilityTheory.IndepFun (fun ω => X i ω - μ) (fun ω => X j ω - μ) P := by
  have hCentered := thm_11_7_centered_independence P X μ hInd
  dsimp [def_5_10_randomVariables] at hCentered
  exact hCentered.indepFun hij

theorem thm_11_7_centered_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hMean : ∀ i : ℕ, P[X i] = μ) (i : ℕ)
    (hXi : Integrable (X i) P) :
    (∫ ω, X i ω - μ ∂P) = 0 := by
  rw [integral_sub hXi (integrable_const μ)]
  simp [hMean i]

theorem thm_11_7_centered_memLp_four_of_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ c : ℝ)
    (hFourth : thm_11_7_centeredFourthMomentUniformBound P X μ c) (i : ℕ) :
    MemLp (fun ω => X i ω - μ) 4 P :=
  (hFourth.2 i).1

theorem thm_11_7_centered_fourth_integral_bound_of_uniform {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ c : ℝ)
    (hFourth : thm_11_7_centeredFourthMomentUniformBound P X μ c) (i : ℕ) :
    (∫ ω, (X i ω - μ) ^ 4 ∂P) ≤ c := by
  rcases (hFourth.2 i).2 with ⟨hXi, hbound⟩
  simpa [rthMoment, generalMoment, moment] using hbound

theorem thm_11_7_centered_integrable_of_uniform {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ c : ℝ)
    (hFourth : thm_11_7_centeredFourthMomentUniformBound P X μ c) (i : ℕ) :
    Integrable (fun ω => X i ω - μ) P :=
  (thm_11_7_centered_memLp_four_of_uniform P X μ c hFourth i).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 4)

theorem thm_11_7_centered_fourth_power_integrable_of_memLp {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ)
    (hY : MemLp Y 4 P) :
    Integrable (fun ω => (Y ω) ^ 4) P := by
  have hNorm : Integrable (fun ω => ‖Y ω‖ ^ (4 : ℝ)) P :=
    hY.integrable_norm_rpow (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ∞)
  refine hNorm.congr (Eventually.of_forall ?_)
  intro ω
  change ‖Y ω‖ ^ (4 : ℝ) = (Y ω) ^ 4
  rw [Real.norm_eq_abs]
  rw [show |Y ω| ^ (4 : ℝ) = |Y ω| ^ (4 : ℕ) by
    exact Real.rpow_natCast |Y ω| 4]
  exact Even.pow_abs (by norm_num : Even 4) (Y ω)

theorem thm_11_7_fourth_centering_pointwise_bound (x μ : ℝ) :
    (x - μ) ^ 4 ≤ 8 * (x ^ 4 + μ ^ 4) := by
  have h1 : (x - μ) ^ 2 ≤ 2 * (x ^ 2 + μ ^ 2) := by
    nlinarith [sq_nonneg (x + μ)]
  have h0 : 0 ≤ (x - μ) ^ 2 := sq_nonneg _
  have hsq : ((x - μ) ^ 2) ^ 2 ≤ (2 * (x ^ 2 + μ ^ 2)) ^ 2 := by
    exact pow_le_pow_left₀ h0 h1 2
  have h2 : (x ^ 2 + μ ^ 2) ^ 2 ≤ 2 * (x ^ 4 + μ ^ 4) := by
    nlinarith [sq_nonneg (x ^ 2 - μ ^ 2)]
  calc
    (x - μ) ^ 4 = ((x - μ) ^ 2) ^ 2 := by ring
    _ ≤ (2 * (x ^ 2 + μ ^ 2)) ^ 2 := hsq
    _ = 4 * (x ^ 2 + μ ^ 2) ^ 2 := by ring
    _ ≤ 4 * (2 * (x ^ 4 + μ ^ 4)) := by nlinarith
    _ = 8 * (x ^ 4 + μ ^ 4) := by ring

theorem thm_11_7_centeredFourthMomentUniformBound_of_fourthMomentUniformBound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ c : ℝ)
    (hFourth : thm_11_7_fourthMomentUniformBound P X μ c) :
    thm_11_7_centeredFourthMomentUniformBound P X μ (8 * (c + μ ^ 4)) := by
  have hμ4_nonneg : 0 ≤ μ ^ 4 := by
    nlinarith [sq_nonneg (μ ^ 2)]
  refine ⟨mul_nonneg (by norm_num) (add_nonneg hFourth.1 hμ4_nonneg), ?_⟩
  intro i
  have hXi4 : MemLp (X i) 4 P := (hFourth.2 i).1
  have hCentered4 : MemLp (fun ω => X i ω - μ) 4 P := by
    convert hXi4.sub (memLp_const (μ := P) μ) using 1
    ext ω
    rfl
  rcases (hFourth.2 i).2 with ⟨hXiFinite, hXiBound⟩
  have hCenteredFinite : FiniteAbsMoment P (fun ω => X i ω - μ) 4 :=
    FiniteAbsMoment.of_memLp (hXiFinite.measurable.sub measurable_const) hCentered4
  refine ⟨hCentered4, hCenteredFinite, ?_⟩
  have hXiPowInt : Integrable (fun ω => (X i ω) ^ 4) P :=
    thm_11_7_centered_fourth_power_integrable_of_memLp P (X i) hXi4
  have hCenteredPowInt : Integrable (fun ω => (X i ω - μ) ^ 4) P :=
    thm_11_7_centered_fourth_power_integrable_of_memLp P
      (fun ω => X i ω - μ) hCentered4
  have hMajorInt : Integrable (fun ω => 8 * ((X i ω) ^ 4 + μ ^ 4)) P :=
    (hXiPowInt.add (integrable_const (μ ^ 4))).const_mul 8
  have hXiMomentBound : (∫ ω, (X i ω) ^ 4 ∂P) ≤ c := by
    simpa [rthMoment, generalMoment, moment] using hXiBound
  calc
    rthMoment P (fun ω => X i ω - μ) positiveOrderFour hCenteredFinite
        = ∫ ω, (X i ω - μ) ^ 4 ∂P := rfl
    _ ≤ ∫ ω, 8 * ((X i ω) ^ 4 + μ ^ 4) ∂P :=
        integral_mono hCenteredPowInt hMajorInt
          (fun ω => thm_11_7_fourth_centering_pointwise_bound (X i ω) μ)
    _ = 8 * ((∫ ω, (X i ω) ^ 4 ∂P) + μ ^ 4) := by
        rw [integral_const_mul]
        rw [integral_add hXiPowInt (integrable_const (μ ^ 4))]
        simp [integral_const]
    _ ≤ 8 * (c + μ ^ 4) := by
        nlinarith [hXiMomentBound]

theorem thm_11_7_centeredPartialSum_fourth_integrable_of_uniform {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ c : ℝ)
    (hFourth : thm_11_7_centeredFourthMomentUniformBound P X μ c) (n : ℕ) :
    Integrable (fun ω => (thm_11_7_centeredPartialSum X μ n ω) ^ 4) P := by
  have hSumMem : MemLp (thm_11_7_centeredPartialSum X μ n) 4 P := by
    change MemLp (fun a => ∑ i : Fin (n + 1), (X i.1 a - μ)) 4 P
    exact memLp_finset_sum (Finset.univ : Finset (Fin (n + 1)))
      (fun i _hi =>
        thm_11_7_centered_memLp_four_of_uniform P X μ c hFourth i.1)
  exact thm_11_7_centered_fourth_power_integrable_of_memLp P
    (thm_11_7_centeredPartialSum X μ n) hSumMem

theorem thm_11_7_centered_pair_product_integral_eq_zero {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hInd : def_5_10_randomVariables P X) {i j : ℕ} (hij : i ≠ j)
    (hXi : AEStronglyMeasurable (fun ω => X i ω - μ) P)
    (hXj : AEStronglyMeasurable (fun ω => X j ω - μ) P)
    (hMeanI : (∫ ω, X i ω - μ ∂P) = 0) :
    (∫ ω, (X i ω - μ) * (X j ω - μ) ∂P) = 0 := by
  have hPair := thm_11_7_centered_pairwise_indepFun P X μ hInd hij
  have hProd := hPair.integral_fun_mul_eq_mul_integral hXi hXj
  simpa [hMeanI] using hProd

theorem thm_11_7_centered_singleton_pair_product_integral_eq_zero {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hInd : def_5_10_randomVariables P X) {i j k : ℕ}
    (hij : i ≠ j) (hik : i ≠ k)
    (hY : ∀ a : ℕ, AEStronglyMeasurable (fun ω => X a ω - μ) P)
    (hMeanI : (∫ ω, X i ω - μ ∂P) = 0) :
    (∫ ω, (X i ω - μ) * ((X j ω - μ) * (X k ω - μ)) ∂P) = 0 := by
  have hCentered := thm_11_7_centered_independence P X μ hInd
  dsimp [def_5_10_randomVariables] at hCentered
  have hPair := hCentered.indepFun_mul_right₀ (fun a => (hY a).aemeasurable) i j k hij hik
  have hRight : AEStronglyMeasurable
      (fun ω => (X j ω - μ) * (X k ω - μ)) P := (hY j).mul (hY k)
  have hProd := hPair.integral_fun_mul_eq_mul_integral (hY i) hRight
  simpa [hMeanI] using hProd

theorem thm_11_7_centered_four_distinct_product_integral_eq_zero {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ)
    (hInd : def_5_10_randomVariables P X) {i j k l : ℕ}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hY : ∀ a : ℕ, AEStronglyMeasurable (fun ω => X a ω - μ) P)
    (hMeanI : (∫ ω, X i ω - μ ∂P) = 0) :
    (∫ ω, (X i ω - μ) * (X j ω - μ) *
        (X k ω - μ) * (X l ω - μ) ∂P) = 0 := by
  let idx : Fin 4 → ℕ := ![i, j, k, l]
  have hidx : Function.Injective idx := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [idx] at hab ⊢
    · exact (hij hab).elim
    · exact (hik hab).elim
    · exact (hil hab).elim
    · exact (hij hab.symm).elim
    · exact (hjk hab).elim
    · exact (hjl hab).elim
    · exact (hik hab.symm).elim
    · exact (hjk hab.symm).elim
    · exact (hkl hab).elim
    · exact (hil hab.symm).elim
    · exact (hjl hab.symm).elim
    · exact (hkl hab.symm).elim
  have hCentered := thm_11_7_centered_independence P X μ hInd
  dsimp [def_5_10_randomVariables] at hCentered
  have hInd4 : ProbabilityTheory.iIndepFun (fun a : Fin 4 => fun ω => X (idx a) ω - μ) P :=
    hCentered.precomp hidx
  have hMeas4 :
      ∀ a : Fin 4, AEStronglyMeasurable (fun ω => X (idx a) ω - μ) P :=
    fun a => hY (idx a)
  have hProd := hInd4.integral_fun_prod_eq_prod_integral hMeas4
  rw [show (fun ω => ∏ a : Fin 4, (X (idx a) ω - μ)) =
      fun ω => (X i ω - μ) * (X j ω - μ) *
        (X k ω - μ) * (X l ω - μ) by
        funext ω
        simp [idx, Fin.prod_univ_four, mul_assoc]] at hProd
  rw [Fin.prod_univ_four] at hProd
  simpa [idx, hMeanI, mul_assoc] using hProd

theorem thm_11_7_centered_fourth_memLp_to_square_memLp {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ) (i : ℕ)
    (hYi4 : MemLp (fun ω => X i ω - μ) 4 P) :
    MemLp (fun ω => (X i ω - μ) ^ 2) 2 P := by
  have h := hYi4.norm_rpow_div 2
  have hExp : (4 : ℝ≥0∞) / 2 = 2 := by
    calc
      (4 : ℝ≥0∞) / 2 = (2 * 2 : ℝ≥0∞) / 2 := by norm_num
      _ = 2 := ENNReal.mul_div_cancel_right (by norm_num) (by simp)
  rw [hExp] at h
  exact (memLp_congr_ae (μ := P)
    (Eventually.of_forall fun ω => by
      simp only [ENNReal.toReal_ofNat]
      rw [Real.rpow_two, Real.norm_eq_abs, sq_abs])).1 h

theorem thm_11_7_paired_square_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ) (i j : ℕ)
    (hXiSq : MemLp (fun ω => (X i ω - μ) ^ 2) (ENNReal.ofReal (2 : ℝ)) P)
    (hXjSq : MemLp (fun ω => (X j ω - μ) ^ 2) (ENNReal.ofReal (2 : ℝ)) P) :
    (∫ ω, (X i ω - μ) ^ 2 * (X j ω - μ) ^ 2 ∂P) ≤
      (∫ ω, (X i ω - μ) ^ 4 ∂P) ^ (1 / (2 : ℝ)) *
        (∫ ω, (X j ω - μ) ^ 4 ∂P) ^ (1 / (2 : ℝ)) := by
  have hCS :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := P) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
      (f := fun ω => (X i ω - μ) ^ 2)
      (g := fun ω => (X j ω - μ) ^ 2)
      (Eventually.of_forall fun ω => sq_nonneg (X i ω - μ))
      (Eventually.of_forall fun ω => sq_nonneg (X j ω - μ))
      hXiSq hXjSq
  have hpow_i :
      (∫ ω, ((X i ω - μ) ^ 2) ^ 2 ∂P) =
        ∫ ω, (X i ω - μ) ^ 4 ∂P := by
    congr with ω
    ring
  have hpow_j :
      (∫ ω, ((X j ω - μ) ^ 2) ^ 2 ∂P) =
        ∫ ω, (X j ω - μ) ^ 4 ∂P := by
    congr with ω
    ring
  simpa [hpow_i, hpow_j] using hCS

def thm_11_7_fourthMomentPartialSumBound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ,
      Integrable (fun ω => (thm_11_7_centeredPartialSum X μ n ω) ^ 4) P ∧
      (∫ ω, (thm_11_7_centeredPartialSum X μ n ω) ^ 4 ∂P) ≤
        C * ((n : ℝ) + 1) ^ 2

theorem thm_11_7_fourth_moment_sum_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ c : ℝ)
    (hInd : def_5_10_randomVariables P X)
    (hMean : ∀ i : ℕ, P[X i] = μ)
    (hFourth : thm_11_7_centeredFourthMomentUniformBound P X μ c) :
    thm_11_7_fourthMomentPartialSumBound P X μ := by
  classical
  refine ⟨3 * c, mul_nonneg (by norm_num) hFourth.1, ?_⟩
  intro n
  constructor
  · exact thm_11_7_centeredPartialSum_fourth_integrable_of_uniform P X μ c hFourth n
  · have hY4 : ∀ i : ℕ, MemLp (fun ω => X i ω - μ) 4 P :=
      fun i => thm_11_7_centered_memLp_four_of_uniform P X μ c hFourth i
    have hYae : ∀ i : ℕ, AEStronglyMeasurable (fun ω => X i ω - μ) P :=
      fun i => (hY4 i).1
    have hXint : ∀ i : ℕ, Integrable (X i) P := by
      intro i
      have hcint := thm_11_7_centered_integrable_of_uniform P X μ c hFourth i
      refine (hcint.add (integrable_const μ)).congr ?_
      filter_upwards with ω
      simp
    have hMeanZero : ∀ i : ℕ, (∫ ω, X i ω - μ ∂P) = 0 :=
      fun i => thm_11_7_centered_mean_zero P X μ hMean i (hXint i)
    have hTermInt : ∀ i j k l : Fin (n + 1),
        Integrable (fun ω => (X i.1 ω - μ) * (X j.1 ω - μ) *
          (X k.1 ω - μ) * (X l.1 ω - μ)) P := by
      intro i j k l
      haveI h44 : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 :=
        NNReal.HolderTriple.coe_ennreal (p := 4) (q := 4) (r := 2)
          (by norm_num)
          (NNReal.HolderTriple.mk (by norm_num) (by norm_num) (by norm_num))
      have hij : MemLp ((fun ω => X i.1 ω - μ) * (fun ω => X j.1 ω - μ)) 2 P :=
        (hY4 j.1).mul (hY4 i.1) (r := (2 : ℝ≥0∞))
      have hkl : MemLp ((fun ω => X k.1 ω - μ) * (fun ω => X l.1 ω - μ)) 2 P :=
        (hY4 l.1).mul (hY4 k.1) (r := (2 : ℝ≥0∞))
      haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 := inferInstance
      have hprod : MemLp
          (((fun ω => X i.1 ω - μ) * (fun ω => X j.1 ω - μ)) *
            ((fun ω => X k.1 ω - μ) * (fun ω => X l.1 ω - μ))) 1 P := hkl.mul hij
      have hint := hprod.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
      convert hint using 1
      ext ω
      simp only [Pi.mul_apply]
      ring
    have hIntegralExpand :
        (∫ ω, (thm_11_7_centeredPartialSum X μ n ω) ^ 4 ∂P) =
          ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            ∑ l : Fin (n + 1),
              ∫ ω, (X i.1 ω - μ) * (X j.1 ω - μ) *
                (X k.1 ω - μ) * (X l.1 ω - μ) ∂P := by
      rw [show (fun ω => (thm_11_7_centeredPartialSum X μ n ω) ^ 4) =
          fun ω => ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            ∑ l : Fin (n + 1),
              (X i.1 ω - μ) * (X j.1 ω - μ) *
                (X k.1 ω - μ) * (X l.1 ω - μ) by
        funext ω
        exact thm_11_7_centeredPartialSum_fourth_expand X μ n ω]
      rw [integral_finset_sum (Finset.univ : Finset (Fin (n + 1))) (fun i _ =>
        integrable_finset_sum (Finset.univ : Finset (Fin (n + 1))) (fun j _ =>
          integrable_finset_sum (Finset.univ : Finset (Fin (n + 1))) (fun k _ =>
            integrable_finset_sum (Finset.univ : Finset (Fin (n + 1)))
              (fun l _ => hTermInt i j k l))))]
      refine Finset.sum_congr rfl ?_
      intro i _hi
      rw [integral_finset_sum (Finset.univ : Finset (Fin (n + 1))) (fun j _ =>
        integrable_finset_sum (Finset.univ : Finset (Fin (n + 1))) (fun k _ =>
          integrable_finset_sum (Finset.univ : Finset (Fin (n + 1)))
            (fun l _ => hTermInt i j k l)))]
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [integral_finset_sum (Finset.univ : Finset (Fin (n + 1))) (fun k _ =>
        integrable_finset_sum (Finset.univ : Finset (Fin (n + 1)))
          (fun l _ => hTermInt i j k l))]
      refine Finset.sum_congr rfl ?_
      intro k _hk
      rw [integral_finset_sum (Finset.univ : Finset (Fin (n + 1)))
        (fun l _ => hTermInt i j k l)]
    have hPairIntegralLe : ∀ a b : Fin (n + 1),
        (∫ ω, (X a.1 ω - μ) ^ 2 * (X b.1 ω - μ) ^ 2 ∂P) ≤ c := by
      intro a b
      have hProd : Integrable (fun ω => (X a.1 ω - μ) ^ 2 *
          (X b.1 ω - μ) ^ 2) P := by
        convert hTermInt a a b b using 1
        ext ω
        ring
      have hA4Int := thm_11_7_centered_fourth_power_integrable_of_memLp P
        (fun ω => X a.1 ω - μ) (hY4 a.1)
      have hB4Int := thm_11_7_centered_fourth_power_integrable_of_memLp P
        (fun ω => X b.1 ω - μ) (hY4 b.1)
      have hAvgInt : Integrable
          (fun ω => ((X a.1 ω - μ) ^ 4 + (X b.1 ω - μ) ^ 4) / 2) P := by
        exact (hA4Int.add hB4Int).div_const 2
      have hPoint : (fun ω => (X a.1 ω - μ) ^ 2 * (X b.1 ω - μ) ^ 2) ≤
          fun ω => ((X a.1 ω - μ) ^ 4 + (X b.1 ω - μ) ^ 4) / 2 := by
        intro ω
        have hs : 0 ≤ ((X a.1 ω - μ) ^ 2 - (X b.1 ω - μ) ^ 2) ^ 2 :=
          sq_nonneg _
        nlinarith
      have hA4Bound := thm_11_7_centered_fourth_integral_bound_of_uniform P X μ c
        hFourth a.1
      have hB4Bound := thm_11_7_centered_fourth_integral_bound_of_uniform P X μ c
        hFourth b.1
      calc
        (∫ ω, (X a.1 ω - μ) ^ 2 * (X b.1 ω - μ) ^ 2 ∂P)
            ≤ ∫ ω, ((X a.1 ω - μ) ^ 4 + (X b.1 ω - μ) ^ 4) / 2 ∂P :=
              integral_mono hProd hAvgInt hPoint
        _ = ((∫ ω, (X a.1 ω - μ) ^ 4 ∂P) +
              (∫ ω, (X b.1 ω - μ) ^ 4 ∂P)) / 2 := by
              rw [integral_div, integral_add hA4Int hB4Int]
        _ ≤ c := by nlinarith
    have hSingletonZero : ∀ {a b d e : ℕ}, a ≠ b → a ≠ d → a ≠ e →
        (∫ ω, (X a ω - μ) * ((X b ω - μ) * (X d ω - μ) * (X e ω - μ)) ∂P) =
          0 := by
      intro a b d e hab had hae
      have hCentered := thm_11_7_centered_independence P X μ hInd
      dsimp [def_5_10_randomVariables] at hCentered
      by_cases hbd : b = d
      · subst d
        by_cases hbe : b = e
        · subst e
          have hPair := thm_11_7_centered_pairwise_indepFun P X μ hInd hab
          have hIndPow : ProbabilityTheory.IndepFun (fun ω => X a ω - μ)
              (fun ω => (X b ω - μ) ^ 3) P := by
            simpa [Function.comp_def] using
              hPair.comp measurable_id (measurable_id.pow_const (3 : ℕ))
          have hRight : AEStronglyMeasurable (fun ω => (X b ω - μ) ^ 3) P := by
            convert (hYae b).pow 3 using 1
            ext ω
            rfl
          have hProd := hIndPow.integral_fun_mul_eq_mul_integral (hYae a) hRight
          simpa [hMeanZero a, pow_succ, pow_two, mul_assoc] using hProd
        · have hPair :=
            (hCentered.indepFun_prodMk₀ (fun t => (hYae t).aemeasurable) b e a
              (by exact fun h => hab h.symm)
              (by exact fun h => hae h.symm)).symm
          have hIndRight : ProbabilityTheory.IndepFun (fun ω => X a ω - μ)
              (fun ω => (X b ω - μ) ^ 2 * (X e ω - μ)) P := by
            simpa [Function.comp_def] using hPair.comp measurable_id
              ((measurable_fst.pow_const (2 : ℕ)).mul measurable_snd)
          have hRight : AEStronglyMeasurable
              (fun ω => (X b ω - μ) ^ 2 * (X e ω - μ)) P := by
            exact ((hYae b).pow 2).mul (hYae e)
          have hProd := hIndRight.integral_fun_mul_eq_mul_integral (hYae a) hRight
          simpa [hMeanZero a, pow_two, mul_assoc, mul_left_comm, mul_comm] using hProd
      · by_cases hbe : b = e
        · subst e
          have hPair :=
            (hCentered.indepFun_prodMk₀ (fun t => (hYae t).aemeasurable) b d a
              (by exact fun h => hab h.symm)
              (by exact fun h => had h.symm)).symm
          have hIndRight : ProbabilityTheory.IndepFun (fun ω => X a ω - μ)
              (fun ω => (X b ω - μ) ^ 2 * (X d ω - μ)) P := by
            simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
              hPair.comp measurable_id ((measurable_fst.pow_const (2 : ℕ)).mul measurable_snd)
          have hRight : AEStronglyMeasurable
              (fun ω => (X b ω - μ) ^ 2 * (X d ω - μ)) P := by
            exact ((hYae b).pow 2).mul (hYae d)
          have hProd := hIndRight.integral_fun_mul_eq_mul_integral (hYae a) hRight
          simpa [hMeanZero a, pow_two, mul_assoc, mul_left_comm, mul_comm] using hProd
        · by_cases hde : d = e
          · subst e
            have hPair :=
              (hCentered.indepFun_prodMk₀ (fun t => (hYae t).aemeasurable) b d a
                (by exact fun h => hab h.symm)
                (by exact fun h => had h.symm)).symm
            have hIndRight : ProbabilityTheory.IndepFun (fun ω => X a ω - μ)
                (fun ω => (X b ω - μ) * (X d ω - μ) ^ 2) P := by
              simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
                hPair.comp measurable_id (measurable_fst.mul (measurable_snd.pow_const (2 : ℕ)))
            have hRight : AEStronglyMeasurable
                (fun ω => (X b ω - μ) * (X d ω - μ) ^ 2) P := by
              exact (hYae b).mul ((hYae d).pow 2)
            have hProd := hIndRight.integral_fun_mul_eq_mul_integral (hYae a) hRight
            simpa [hMeanZero a, pow_two, mul_assoc, mul_left_comm, mul_comm] using hProd
          · have hzero := thm_11_7_centered_four_distinct_product_integral_eq_zero P X μ hInd
                hab had hae hbd hbe hde hYae (hMeanZero a)
            simpa [mul_assoc] using hzero
    have hMixedZero : ∀ i j k l : Fin (n + 1),
        ¬ (i = j ∧ k = l) → ¬ (i = k ∧ j = l) → ¬ (i = l ∧ j = k) →
        (∫ ω, (X i.1 ω - μ) * (X j.1 ω - μ) *
            (X k.1 ω - μ) * (X l.1 ω - μ) ∂P) = 0 := by
      intro i j k l hnot1 hnot2 hnot3
      by_cases hij : i = j
      · subst j
        have hkl : k ≠ l := by
          intro h
          exact hnot1 ⟨rfl, h⟩
        by_cases hik : i = k
        · subst k
          have hli : l.1 ≠ i.1 := by
            intro h
            exact hkl (Fin.ext h.symm)
          have hZ := hSingletonZero (a := l.1) (b := i.1) (d := i.1) (e := i.1)
            hli hli hli
          simpa [mul_assoc, mul_left_comm, mul_comm] using hZ
        · by_cases hil : i = l
          · subst l
            have hki : k.1 ≠ i.1 := by
              intro h
              exact hik (Fin.ext h.symm)
            have hZ := hSingletonZero (a := k.1) (b := i.1) (d := i.1) (e := i.1)
              hki hki hki
            simpa [mul_assoc, mul_left_comm, mul_comm] using hZ
          · have hki : k.1 ≠ i.1 := by
              intro h
              exact hik (Fin.ext h.symm)
            have hklNat : k.1 ≠ l.1 := by
              intro h
              exact hkl (Fin.ext h)
            have hZ := hSingletonZero (a := k.1) (b := i.1) (d := i.1) (e := l.1)
              hki hki hklNat
            simpa [mul_assoc, mul_left_comm, mul_comm] using hZ
      · by_cases hik : i = k
        · subst k
          have hjl : j ≠ l := by
            intro h
            exact hnot2 ⟨rfl, h⟩
          by_cases hil : i = l
          · subst l
            have hji : j.1 ≠ i.1 := by
              intro h
              exact hij (Fin.ext h.symm)
            have hZ := hSingletonZero (a := j.1) (b := i.1) (d := i.1) (e := i.1)
              hji hji hji
            simpa [mul_assoc, mul_left_comm, mul_comm] using hZ
          · have hji : j.1 ≠ i.1 := by
              intro h
              exact hij (Fin.ext h.symm)
            have hjlNat : j.1 ≠ l.1 := by
              intro h
              exact hjl (Fin.ext h)
            have hZ := hSingletonZero (a := j.1) (b := i.1) (d := i.1) (e := l.1)
              hji hji hjlNat
            simpa [mul_assoc, mul_left_comm, mul_comm] using hZ
        · by_cases hil : i = l
          · subst l
            have hjk : j ≠ k := by
              intro h
              exact hnot3 ⟨rfl, h⟩
            have hji : j.1 ≠ i.1 := by
              intro h
              exact hij (Fin.ext h.symm)
            have hjkNat : j.1 ≠ k.1 := by
              intro h
              exact hjk (Fin.ext h)
            have hZ := hSingletonZero (a := j.1) (b := i.1) (d := k.1) (e := i.1)
              hji hjkNat hji
            simpa [mul_assoc, mul_left_comm, mul_comm] using hZ
          · have hijNat : i.1 ≠ j.1 := by
              intro h
              exact hij (Fin.ext h)
            have hikNat : i.1 ≠ k.1 := by
              intro h
              exact hik (Fin.ext h)
            have hilNat : i.1 ≠ l.1 := by
              intro h
              exact hil (Fin.ext h)
            have hZ := hSingletonZero (a := i.1) (b := j.1) (d := k.1) (e := l.1)
              hijNat hikNat hilNat
            simpa [mul_assoc] using hZ
    have hTermBound : ∀ i j k l : Fin (n + 1),
        (∫ ω, (X i.1 ω - μ) * (X j.1 ω - μ) *
            (X k.1 ω - μ) * (X l.1 ω - μ) ∂P) ≤
          (if i = j ∧ k = l then c else 0) +
          (if i = k ∧ j = l then c else 0) +
          (if i = l ∧ j = k then c else 0) := by
      intro i j k l
      by_cases h1 : i = j ∧ k = l
      · have hle_c :
            (∫ ω, (X i.1 ω - μ) * (X j.1 ω - μ) *
                (X k.1 ω - μ) * (X l.1 ω - μ) ∂P) ≤ c := by
          rcases h1 with ⟨hij, hkl⟩
          subst j
          subst l
          simpa [pow_two, mul_assoc] using hPairIntegralLe i k
        have hA : 0 ≤ (if i = k ∧ j = l then c else 0) := by
          by_cases h : i = k ∧ j = l <;> simp [h, hFourth.1]
        have hB : 0 ≤ (if i = l ∧ j = k then c else 0) := by
          by_cases h : i = l ∧ j = k <;> simp [h, hFourth.1]
        have hRhs : c ≤ (if i = j ∧ k = l then c else 0) +
            (if i = k ∧ j = l then c else 0) +
            (if i = l ∧ j = k then c else 0) := by
          have hfirst : (if i = j ∧ k = l then c else 0) = c := by simp [h1]
          nlinarith
        exact hle_c.trans hRhs
      · by_cases h2 : i = k ∧ j = l
        · have hle_c :
              (∫ ω, (X i.1 ω - μ) * (X j.1 ω - μ) *
                  (X k.1 ω - μ) * (X l.1 ω - μ) ∂P) ≤ c := by
            rcases h2 with ⟨hik, hjl⟩
            subst k
            subst l
            simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hPairIntegralLe i j
          have hA : 0 ≤ (if i = j ∧ k = l then c else 0) := by
            by_cases h : i = j ∧ k = l <;> simp [h, hFourth.1]
          have hB : 0 ≤ (if i = l ∧ j = k then c else 0) := by
            by_cases h : i = l ∧ j = k <;> simp [h, hFourth.1]
          have hRhs : c ≤ (if i = j ∧ k = l then c else 0) +
              (if i = k ∧ j = l then c else 0) +
              (if i = l ∧ j = k then c else 0) := by
            have hsecond : (if i = k ∧ j = l then c else 0) = c := by simp [h2]
            nlinarith
          exact hle_c.trans hRhs
        · by_cases h3 : i = l ∧ j = k
          · have hle_c :
                (∫ ω, (X i.1 ω - μ) * (X j.1 ω - μ) *
                    (X k.1 ω - μ) * (X l.1 ω - μ) ∂P) ≤ c := by
              rcases h3 with ⟨hil, hjk⟩
              subst l
              subst k
              simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hPairIntegralLe i j
            have hA : 0 ≤ (if i = j ∧ k = l then c else 0) := by
              by_cases h : i = j ∧ k = l <;> simp [h, hFourth.1]
            have hB : 0 ≤ (if i = k ∧ j = l then c else 0) := by
              by_cases h : i = k ∧ j = l <;> simp [h, hFourth.1]
            have hRhs : c ≤ (if i = j ∧ k = l then c else 0) +
                (if i = k ∧ j = l then c else 0) +
                (if i = l ∧ j = k then c else 0) := by
              have hthird : (if i = l ∧ j = k then c else 0) = c := by simp [h3]
              nlinarith
            exact hle_c.trans hRhs
          · have hzero := hMixedZero i j k l h1 h2 h3
            simp [hzero, h1, h2, h3]
    have hPairingCount :
        (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
          ((if i = j ∧ k = l then c else 0) +
           (if i = k ∧ j = l then c else 0) +
           (if i = l ∧ j = k then c else 0))) =
          3 * (((n : ℝ) + 1) ^ 2 * c) := by
      have h1c :
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            ∑ l : Fin (n + 1), if i = j ∧ k = l then c else 0) =
            ((n : ℝ) + 1) ^ 2 * c := by
        calc
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            ∑ l : Fin (n + 1), if i = j ∧ k = l then c else 0)
              = ∑ i : Fin (n + 1), ∑ k : Fin (n + 1), c := by
                congr with i
                rw [Fintype.sum_eq_single i]
                · congr with k
                  rw [Fintype.sum_eq_single k]
                  · simp
                  · intro l hl
                    have hne : ¬ k = l := fun h => hl h.symm
                    simp [hne]
                · intro j hj
                  have hne : ¬ i = j := fun h => hj h.symm
                  simp [hne]
          _ = ((n : ℝ) + 1) ^ 2 * c := by
            simp [Fintype.card_fin]
            ring
      have h2c :
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            ∑ l : Fin (n + 1), if i = k ∧ j = l then c else 0) =
            ((n : ℝ) + 1) ^ 2 * c := by
        calc
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            ∑ l : Fin (n + 1), if i = k ∧ j = l then c else 0)
              = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), c := by
                congr with i
                congr with j
                rw [Fintype.sum_eq_single i]
                · rw [Fintype.sum_eq_single j]
                  · simp
                  · intro l hl
                    have hne : ¬ j = l := fun h => hl h.symm
                    simp [hne]
                · intro k hk
                  have hne : ¬ i = k := fun h => hk h.symm
                  simp [hne]
          _ = ((n : ℝ) + 1) ^ 2 * c := by
            simp [Fintype.card_fin]
            ring
      have h3c :
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            ∑ l : Fin (n + 1), if i = l ∧ j = k then c else 0) =
            ((n : ℝ) + 1) ^ 2 * c := by
        calc
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
            ∑ l : Fin (n + 1), if i = l ∧ j = k then c else 0)
              = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), c := by
                congr with i
                congr with j
                rw [Fintype.sum_eq_single j]
                · rw [Fintype.sum_eq_single i]
                  · simp
                  · intro l hl
                    have hne : ¬ i = l := fun h => hl h.symm
                    simp [hne]
                · intro k hk
                  have hne : ¬ j = k := fun h => hk h.symm
                  simp [hne]
          _ = ((n : ℝ) + 1) ^ 2 * c := by
            simp [Fintype.card_fin]
            ring
      simp_rw [Finset.sum_add_distrib]
      rw [h1c, h2c, h3c]
      ring
    calc
      (∫ ω, (thm_11_7_centeredPartialSum X μ n ω) ^ 4 ∂P)
          = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
              ∑ l : Fin (n + 1),
                ∫ ω, (X i.1 ω - μ) * (X j.1 ω - μ) *
                  (X k.1 ω - μ) * (X l.1 ω - μ) ∂P := hIntegralExpand
      _ ≤ ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
              ∑ l : Fin (n + 1),
                ((if i = j ∧ k = l then c else 0) +
                 (if i = k ∧ j = l then c else 0) +
                 (if i = l ∧ j = k then c else 0)) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            refine Finset.sum_le_sum ?_
            intro j _hj
            refine Finset.sum_le_sum ?_
            intro k _hk
            refine Finset.sum_le_sum ?_
            intro l _hl
            exact hTermBound i j k l
      _ = 3 * (((n : ℝ) + 1) ^ 2 * c) := hPairingCount
      _ = (3 * c) * ((n : ℝ) + 1) ^ 2 := by ring

theorem thm_11_7_pseries_tail_bound (C : ℝ) (hC : 0 ≤ C) :
    (∑' n : ℕ, ENNReal.ofReal (C * (1 / |(n : ℝ) + 1| ^ (2 : ℝ)))) ≠ ∞ := by
  have hs0 : Summable fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (2 : ℝ) := by
    exact (Real.summable_one_div_nat_add_rpow 1 (2 : ℝ)).2 (by norm_num)
  have hs : Summable fun n : ℕ => C * (1 / |(n : ℝ) + 1| ^ (2 : ℝ)) := by
    exact hs0.mul_left C
  have hnonneg :
      ∀ n : ℕ, 0 ≤ C * (1 / |(n : ℝ) + 1| ^ (2 : ℝ)) := by
    intro n
    exact mul_nonneg hC (by positivity)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hs]
  exact ENNReal.ofReal_ne_top

theorem thm_11_7_sampleMean_sub_mean_eq_centeredPartialSum_div {Ω : Type*}
    (X : ℕ → Ω → ℝ) (μ : ℝ) (n : ℕ) (ω : Ω) :
    thm_11_5_sampleMean X n ω - μ =
      thm_11_7_centeredPartialSum X μ n ω / ((n : ℝ) + 1) := by
  have hN : (n : ℝ) + 1 ≠ 0 := by positivity
  simp [thm_11_5_sampleMean, thm_11_7_centeredPartialSum,
    Finset.sum_sub_distrib, Finset.sum_const, Fintype.card_fin,
    div_eq_mul_inv]
  field_simp [hN]

theorem thm_11_7_markov_fourth_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (μ : ℝ)
    (n : ℕ)
    (hInt : Integrable (fun ω => (thm_11_7_centeredPartialSum X μ n ω) ^ 4) P)
    {ε : ℝ} (hε : 0 < ε) :
    P (almostSureDeviationEvent
        (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε) ≤
      ENNReal.ofReal
        ((∫ ω, (thm_11_7_centeredPartialSum X μ n ω) ^ 4 ∂P) /
          ((ε * ((n : ℝ) + 1)) ^ 4)) := by
  let threshold := (ε * ((n : ℝ) + 1)) ^ 4
  have hNpos : 0 < (n : ℝ) + 1 := by positivity
  have hthreshold_pos : 0 < threshold := by
    dsimp [threshold]
    positivity
  have hMarkov :
      P.real {ω : Ω | threshold ≤ (thm_11_7_centeredPartialSum X μ n ω) ^ 4} ≤
        (∫ ω, (thm_11_7_centeredPartialSum X μ n ω) ^ 4 ∂P) / threshold := by
    exact thm_10_3 P
      (fun ω => (thm_11_7_centeredPartialSum X μ n ω) ^ 4)
      (Eventually.of_forall fun ω => by positivity)
      hInt hthreshold_pos
  have hsubset :
      almostSureDeviationEvent
          (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε ⊆
        {ω : Ω | threshold ≤ (thm_11_7_centeredPartialSum X μ n ω) ^ 4} := by
    intro ω hω
    have hdev :
        ε < |thm_11_5_sampleMean X n ω - μ| := by
      simpa [almostSureDeviationEvent] using hω
    have hscaled :
        ε < |thm_11_7_centeredPartialSum X μ n ω| / ((n : ℝ) + 1) := by
      simpa [thm_11_7_sampleMean_sub_mean_eq_centeredPartialSum_div,
        abs_div, abs_of_pos hNpos] using hdev
    have hmul := mul_lt_mul_of_pos_right hscaled hNpos
    have hbase_lt :
        ε * ((n : ℝ) + 1) < |thm_11_7_centeredPartialSum X μ n ω| := by
      simpa [div_mul_cancel₀ _ hNpos.ne'] using hmul
    have hpow :
        (ε * ((n : ℝ) + 1)) ^ 4 ≤
          |thm_11_7_centeredPartialSum X μ n ω| ^ 4 := by
      exact pow_le_pow_left₀ (by positivity) (le_of_lt hbase_lt) 4
    dsimp [threshold]
    simpa [Even.pow_abs (by norm_num : Even 4)
      (thm_11_7_centeredPartialSum X μ n ω)] using hpow
  have hfinite :
      P (almostSureDeviationEvent
        (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε) ≠ ∞ := by
    exact measure_ne_top P _
  rw [← MeasureTheory.ofReal_measureReal hfinite]
  have hmono :
      P.real (almostSureDeviationEvent
          (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε) ≤
        P.real {ω : Ω | threshold ≤ (thm_11_7_centeredPartialSum X μ n ω) ^ 4} := by
    exact measureReal_mono (μ := P) hsubset
  exact ENNReal.ofReal_le_ofReal (by
    simpa [threshold] using le_trans hmono hMarkov)

theorem thm_11_7_fourth_moment_ratio_eq_pseries_term
    (C ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    (C * ((n : ℝ) + 1) ^ 2) / ((ε * ((n : ℝ) + 1)) ^ 4) =
      (C / ε ^ 4) * (1 / |(n : ℝ) + 1| ^ (2 : ℝ)) := by
  have hNpos : 0 < (n : ℝ) + 1 := by positivity
  rw [abs_of_pos hNpos]
  rw [show ((n : ℝ) + 1) ^ (2 : ℝ) = ((n : ℝ) + 1) ^ 2 by
    exact Real.rpow_natCast ((n : ℝ) + 1) 2]
  field_simp [hε.ne', hNpos.ne']

def thm_11_7_tailSummabilitySupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (μ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (∑' n : ℕ,
      P (almostSureDeviationEvent
        (fun n => thm_11_5_sampleMean X n) (fun _ : Ω => μ) n ε)) ≠ ∞

theorem thm_11_7_tail_summability_from_partial_sum_bound {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : ℝ) :
    thm_11_7_fourthMomentPartialSumBound P X μ →
    thm_11_7_tailSummabilitySupport P X μ := by
  rintro ⟨C, hC_nonneg, hC_bound⟩ ε hε
  have hCoeff_nonneg : 0 ≤ C / ε ^ 4 := by
    exact div_nonneg hC_nonneg (pow_nonneg hε.le 4)
  refine ne_top_of_le_ne_top
    (thm_11_7_pseries_tail_bound (C / ε ^ 4) hCoeff_nonneg) ?_
  refine ENNReal.tsum_le_tsum ?_
  intro n
  rcases hC_bound n with ⟨hInt, hMoment⟩
  refine (thm_11_7_markov_fourth_tail_bound P X μ n hInt hε).trans ?_
  have hden_nonneg : 0 ≤ (ε * ((n : ℝ) + 1)) ^ 4 := by positivity
  have hReal :
      (∫ ω, (thm_11_7_centeredPartialSum X μ n ω) ^ 4 ∂P) /
          ((ε * ((n : ℝ) + 1)) ^ 4) ≤
        (C / ε ^ 4) * (1 / |(n : ℝ) + 1| ^ (2 : ℝ)) := by
    calc
      (∫ ω, (thm_11_7_centeredPartialSum X μ n ω) ^ 4 ∂P) /
          ((ε * ((n : ℝ) + 1)) ^ 4)
          ≤ (C * ((n : ℝ) + 1) ^ 2) /
              ((ε * ((n : ℝ) + 1)) ^ 4) := by
            exact div_le_div_of_nonneg_right hMoment hden_nonneg
      _ = (C / ε ^ 4) * (1 / |(n : ℝ) + 1| ^ (2 : ℝ)) := by
            exact thm_11_7_fourth_moment_ratio_eq_pseries_term C ε hε n
  exact ENNReal.ofReal_le_ofReal hReal

theorem thm_11_7_tail_summability_from_fourth_moment {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ : ℝ) :
    def_5_10_randomVariables P X →
    (∀ i : ℕ, P[X i] = μ) →
    (∃ c : ℝ, thm_11_7_fourthMomentUniformBound P X μ c) →
    thm_11_7_tailSummabilitySupport P X μ := by
  intro hInd hMean hFourth
  rcases hFourth with ⟨c, hFourth⟩
  have hCenteredFourth :
      thm_11_7_centeredFourthMomentUniformBound P X μ (8 * (c + μ ^ 4)) :=
    thm_11_7_centeredFourthMomentUniformBound_of_fourthMomentUniformBound
      P X μ c hFourth
  exact thm_11_7_tail_summability_from_partial_sum_bound P X μ
    (thm_11_7_fourth_moment_sum_bound P X μ (8 * (c + μ ^ 4)) hInd hMean
      hCenteredFourth)
