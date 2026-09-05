/-
TASK ID: prob_12_3
TYPE: Problem
SOURCE PLAN: chapter12-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.def_12_2
import ProbabilityTheory.chapter_12.def_12_5
import ProbabilityTheory.chapter_12.thm_12_5




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace

noncomputable section

 
def prob_12_3_exponentialMeasure : Measure ℝ :=
  expMeasure 1

instance prob_12_3_exponentialMeasure_isProbability :
    IsProbabilityMeasure prob_12_3_exponentialMeasure :=
  isProbabilityMeasure_expMeasure (by norm_num)



theorem prob_12_3_integral_eq_weighted (g : ℝ → ℝ) :
    ∫ x, g x ∂prob_12_3_exponentialMeasure =
      ∫ x in Set.Ioi 0, g x * Real.exp (-x) := by
  change
    ∫ x, g x ∂volume.withDensity (exponentialPDF 1) =
      ∫ x in Set.Ioi 0, g x * Real.exp (-x)
  rw [show exponentialPDF 1 =
    (fun x => ENNReal.ofReal (exponentialPDFReal 1 x)) from rfl]
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_exponentialPDFReal 1).ennreal_ofReal (by simp)]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with x hx
  by_cases hpos : 0 < x
  · have hdensity : exponentialPDFReal 1 x = Real.exp (-x) := by
      simp [exponentialPDFReal, gammaPDFReal, hpos.le]
    rw [hdensity, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    simp [hpos, mul_comm]
  · have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
    have hdensity : exponentialPDFReal 1 x = 0 := by
      simp [exponentialPDFReal, gammaPDFReal, not_le.mpr hneg]
    rw [hdensity]
    simp [hpos]

 
theorem prob_12_3_exponential_total_mass :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-x) = 1 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := 1) (by norm_num) (by norm_num)
  simpa using h

 
theorem prob_12_3_exponential_second_moment :
    ∫ x : ℝ in Set.Ioi 0, x ^ 2 * Real.exp (-x) = 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3) (r := 1) (by norm_num) (by norm_num)
  norm_num at h
  exact h

 
theorem prob_12_3_exponential_fourth_moment :
    ∫ x : ℝ in Set.Ioi 0, x ^ 4 * Real.exp (-x) = 24 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 5) (r := 1) (by norm_num) (by norm_num)
  norm_num at h
  exact h

theorem prob_12_3_integral_square :
    ∫ x : ℝ, x ^ 2 ∂prob_12_3_exponentialMeasure = 2 := by
  rw [prob_12_3_integral_eq_weighted]
  exact prob_12_3_exponential_second_moment

theorem prob_12_3_integral_fourth :
    ∫ x : ℝ, x ^ 4 ∂prob_12_3_exponentialMeasure = 24 := by
  rw [prob_12_3_integral_eq_weighted]
  exact prob_12_3_exponential_fourth_moment



theorem prob_12_3_square_memL2 :
    L2Function prob_12_3_exponentialMeasure (fun x : ℝ => x ^ 2) := by
  change MemLp (fun x : ℝ => x ^ 2) 2 prob_12_3_exponentialMeasure
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        prob_12_3_exponentialMeasure :=
    (measurable_id.pow_const 2).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hmeas).2 ?_
  have h4 : Integrable (fun x : ℝ => x ^ 4) prob_12_3_exponentialMeasure :=
    Integrable.of_integral_ne_zero (by
      rw [prob_12_3_integral_fourth]
      norm_num)
  exact h4.congr (ae_of_all _ fun x => by ring)

 
def prob_12_3_squareL2 : ℝ →₂[prob_12_3_exponentialMeasure] ℝ :=
  (show MemLp (fun x : ℝ => x ^ 2) 2 prob_12_3_exponentialMeasure from
    prob_12_3_square_memL2).toLp (fun x : ℝ => x ^ 2)



def prob_12_3_oneL2 : ℝ →₂[prob_12_3_exponentialMeasure] ℝ :=
  Lp.const 2 prob_12_3_exponentialMeasure 1

 
def prob_12_3_constantL2 (c : ℝ) : ℝ →₂[prob_12_3_exponentialMeasure] ℝ :=
  c • prob_12_3_oneL2

 
def prob_12_3_constantSubmodule :
    Submodule ℝ (ℝ →₂[prob_12_3_exponentialMeasure] ℝ) :=
  ℝ ∙ prob_12_3_oneL2

instance prob_12_3_constantSubmodule_finiteDimensional :
    FiniteDimensional ℝ prob_12_3_constantSubmodule := by
  exact Module.Finite.of_fg
    (Submodule.fg_span (Set.finite_singleton prob_12_3_oneL2))



def prob_12_3_constantClosedSubmodule :
    ClosedSubmodule ℝ (ℝ →₂[prob_12_3_exponentialMeasure] ℝ) :=
  ClosedSubmodule.mk prob_12_3_constantSubmodule
    (Submodule.closed_of_finiteDimensional prob_12_3_constantSubmodule)

theorem prob_12_3_constantL2_mem (c : ℝ) :
    prob_12_3_constantL2 c ∈ prob_12_3_constantClosedSubmodule := by
  exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩



def prob_12_3_projectionCandidate : prob_12_3_constantClosedSubmodule :=
  ⟨prob_12_3_constantL2 2, prob_12_3_constantL2_mem 2⟩

theorem prob_12_3_square_inner_one :
    ⟪prob_12_3_squareL2, prob_12_3_oneL2⟫_ℝ = 2 := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, ⟪prob_12_3_squareL2 x, prob_12_3_oneL2 x⟫_ℝ
        ∂prob_12_3_exponentialMeasure) =
        ∫ x : ℝ, x ^ 2 ∂prob_12_3_exponentialMeasure := by
          apply integral_congr_ae
          filter_upwards [MemLp.coeFn_toLp prob_12_3_square_memL2,
            Lp.coeFn_const (μ := prob_12_3_exponentialMeasure)
              (p := (2 : ENNReal)) (1 : ℝ)]
            with x hx h1
          simp [prob_12_3_squareL2, prob_12_3_oneL2, hx]
    _ = 2 := prob_12_3_integral_square

theorem prob_12_3_one_inner_one :
    ⟪prob_12_3_oneL2, prob_12_3_oneL2⟫_ℝ = 1 := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x, ⟪prob_12_3_oneL2 x, prob_12_3_oneL2 x⟫_ℝ
        ∂prob_12_3_exponentialMeasure) =
        ∫ _ : ℝ, (1 : ℝ) ∂prob_12_3_exponentialMeasure := by
          apply integral_congr_ae
          filter_upwards [
            Lp.coeFn_const (μ := prob_12_3_exponentialMeasure)
              (p := (2 : ENNReal)) (1 : ℝ)]
            with x h1
          simp [prob_12_3_oneL2]
    _ = 1 := by simp



theorem prob_12_3_projection_orthogonal :
    ∀ Z : prob_12_3_constantClosedSubmodule,
      ⟪prob_12_3_squareL2 -
          (prob_12_3_projectionCandidate :
            ℝ →₂[prob_12_3_exponentialMeasure] ℝ),
        (Z : ℝ →₂[prob_12_3_exponentialMeasure] ℝ)⟫_ℝ = 0 := by
  intro Z
  rcases Submodule.mem_span_singleton.mp Z.2 with ⟨c, hc⟩
  change
    ⟪prob_12_3_squareL2 - prob_12_3_constantL2 2,
      (Z : ℝ →₂[prob_12_3_exponentialMeasure] ℝ)⟫_ℝ = 0
  rw [← hc]
  simp only [prob_12_3_constantL2, inner_smul_right, inner_sub_left,
    inner_smul_left]
  rw [prob_12_3_square_inner_one, prob_12_3_one_inner_one]
  simp



theorem prob_12_3 :
    prob_12_3_projectionCandidate =
      def_12_5 prob_12_3_exponentialMeasure
        prob_12_3_constantClosedSubmodule prob_12_3_squareL2 := by
  exact (thm_12_5 prob_12_3_exponentialMeasure
    prob_12_3_constantClosedSubmodule prob_12_3_squareL2
    prob_12_3_projectionCandidate).2 prob_12_3_projection_orthogonal

 
theorem prob_12_3_mse_minimal (c : ℝ) :
    ‖prob_12_3_squareL2 -
        (prob_12_3_projectionCandidate :
          ℝ →₂[prob_12_3_exponentialMeasure] ℝ)‖ ^ 2 ≤
      ‖prob_12_3_squareL2 - prob_12_3_constantL2 c‖ ^ 2 := by
  have hmin := def_12_5_minimizes prob_12_3_exponentialMeasure
    prob_12_3_constantClosedSubmodule prob_12_3_squareL2
  rw [← prob_12_3] at hmin
  have hnorm :
      ‖prob_12_3_squareL2 -
          (prob_12_3_projectionCandidate :
            ℝ →₂[prob_12_3_exponentialMeasure] ℝ)‖ ≤
        ‖prob_12_3_squareL2 - prob_12_3_constantL2 c‖ := by
    rw [hmin]
    have hbounded : BddBelow (Set.range
        (fun U : prob_12_3_constantClosedSubmodule =>
          ‖prob_12_3_squareL2 -
            (U : ℝ →₂[prob_12_3_exponentialMeasure] ℝ)‖)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨U, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbounded
      (⟨prob_12_3_constantL2 c, prob_12_3_constantL2_mem c⟩ :
        prob_12_3_constantClosedSubmodule)
  nlinarith [norm_nonneg
    (prob_12_3_squareL2 -
      (prob_12_3_projectionCandidate :
        ℝ →₂[prob_12_3_exponentialMeasure] ℝ)),
    norm_nonneg (prob_12_3_squareL2 - prob_12_3_constantL2 c)]

 
theorem prob_12_3_mse_unique
    (Z : prob_12_3_constantClosedSubmodule)
    (hZ :
      ‖prob_12_3_squareL2 -
          (Z : ℝ →₂[prob_12_3_exponentialMeasure] ℝ)‖ ^ 2 =
        ‖prob_12_3_squareL2 -
          (prob_12_3_projectionCandidate :
            ℝ →₂[prob_12_3_exponentialMeasure] ℝ)‖ ^ 2) :
    Z = prob_12_3_projectionCandidate := by
  have hZnorm :
      ‖prob_12_3_squareL2 -
          (Z : ℝ →₂[prob_12_3_exponentialMeasure] ℝ)‖ =
        ‖prob_12_3_squareL2 -
          (prob_12_3_projectionCandidate :
            ℝ →₂[prob_12_3_exponentialMeasure] ℝ)‖ := by
    nlinarith [norm_nonneg
      (prob_12_3_squareL2 -
        (Z : ℝ →₂[prob_12_3_exponentialMeasure] ℝ)),
      norm_nonneg
        (prob_12_3_squareL2 -
          (prob_12_3_projectionCandidate :
            ℝ →₂[prob_12_3_exponentialMeasure] ℝ))]
  have hmin := def_12_5_minimizes prob_12_3_exponentialMeasure
    prob_12_3_constantClosedSubmodule prob_12_3_squareL2
  rw [← prob_12_3] at hmin
  have hZmin :
      ‖prob_12_3_squareL2 -
          (Z : ℝ →₂[prob_12_3_exponentialMeasure] ℝ)‖ =
        ⨅ U : prob_12_3_constantClosedSubmodule,
          ‖prob_12_3_squareL2 -
            (U : ℝ →₂[prob_12_3_exponentialMeasure] ℝ)‖ :=
    hZnorm.trans hmin
  calc
    Z = def_12_5 prob_12_3_exponentialMeasure
        prob_12_3_constantClosedSubmodule prob_12_3_squareL2 :=
      def_12_5_unique prob_12_3_exponentialMeasure
        prob_12_3_constantClosedSubmodule prob_12_3_squareL2 Z hZmin
    _ = prob_12_3_projectionCandidate := prob_12_3.symm
