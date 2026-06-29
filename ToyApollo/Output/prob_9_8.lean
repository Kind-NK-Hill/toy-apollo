import Mathlib
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_9_6
import ToyApollo.Output.thm_9_3

/-
TASK ID: prob_9_8
TYPE: Problem
SOURCE PLAN: chapter9-problems
TASK CONTENT:
\textbf{Problem 9.8} Prove that $\phi_X(2\pi)=1$ if and only if $P(X\in\mathbb{Z})=1$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped Topology

noncomputable section

def integerRange : Set ℝ :=
  Set.range fun k : ℤ => (k : ℝ)

def IntegerValuedAE {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, X ω ∈ integerRange

lemma measurableSet_integerRange : MeasurableSet integerRange := by
  exact (Set.countable_range fun k : ℤ => (k : ℝ)).measurableSet

lemma exp_two_pi_I_eq_one_iff_integerRange (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = 1 ↔
      x ∈ integerRange := by
  constructor
  · intro hx
    rcases Complex.exp_eq_one_iff.mp hx with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have him :
        (Complex.I * (x : ℂ) * ((2 * Real.pi : ℝ) : ℂ)).im =
          (n * (2 * Real.pi * Complex.I : ℂ)).im := by
      rw [hn]
    have hreal : x * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by
      simpa [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_assoc, mul_left_comm, mul_comm]
        using him
    have hnonzero : 2 * Real.pi ≠ 0 := by
      exact mul_ne_zero (by norm_num) Real.pi_ne_zero
    exact (mul_right_cancel₀ hnonzero hreal).symm
  · rintro ⟨n, rfl⟩
    rw [Complex.exp_eq_one_iff]
    refine ⟨n, ?_⟩
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, mul_assoc, mul_left_comm, mul_comm]

lemma complex_unit_integral_eq_one_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℂ}
    (hYint : Integrable Y P)
    (hYnorm : ∀ᵐ ω ∂P, ‖Y ω‖ = 1)
    (hYintegral : ∫ ω, Y ω ∂P = 1) :
    Y =ᵐ[P] fun _ => (1 : ℂ) := by
  let g : Ω → ℝ := fun ω => 1 - RCLike.re (Y ω)
  have hg_nonneg : 0 ≤ᵐ[P] g := by
    filter_upwards [hYnorm] with ω hnorm
    have hre_le : RCLike.re (Y ω) ≤ ‖Y ω‖ := RCLike.re_le_norm (Y ω)
    have hre_le_one : RCLike.re (Y ω) ≤ 1 := by
      simpa [hnorm] using hre_le
    dsimp [g]
    exact sub_nonneg.mpr hre_le_one
  have hg_int : Integrable g P := by
    exact (integrable_const (1 : ℝ)).sub hYint.re
  have hg_zero : ∫ ω, g ω ∂P = 0 := by
    calc
      ∫ ω, g ω ∂P =
          ∫ ω, (1 : ℝ) ∂P - ∫ ω, RCLike.re (Y ω) ∂P := by
            simpa [g] using
              (integral_sub (integrable_const (1 : ℝ)) hYint.re)
      _ = 1 - RCLike.re (∫ ω, Y ω ∂P) := by
            have hone : ∫ _ω : Ω, (1 : ℝ) ∂P = 1 := by
              simp
            rw [hone, integral_re hYint]
            rfl
      _ = 0 := by
            rw [hYintegral]
            simp
  have hg_ae : g =ᵐ[P] fun _ => 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hg_nonneg hg_int).mp hg_zero
  filter_upwards [hg_ae, hYnorm] with ω hgω hnormω
  have hre : RCLike.re (Y ω) = 1 := by
    dsimp [g] at hgω
    change (Y ω).re = 1
    linarith
  have hle : ‖Y ω‖ ≤ RCLike.re (Y ω) := by
    rw [hnormω, hre]
  have hcomplex : (RCLike.re (Y ω) : ℂ) = Y ω :=
    RCLike.re_eq_self_of_le hle
  calc
    Y ω = (RCLike.re (Y ω) : ℂ) := hcomplex.symm
    _ = 1 := by simp [hre]

lemma characteristic_integrand_two_pi_norm
    {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) :
    ∀ ω, ‖Complex.exp (Complex.I * (X ω : ℂ) * ((2 * Real.pi : ℝ) : ℂ))‖ = 1 := by
  intro ω
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, mul_assoc, mul_left_comm,
    mul_comm]

theorem characteristicFunction_two_pi_eq_one_iff_integerValuedAE
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) :
    characteristicFunction P X (2 * Real.pi) = 1 ↔ IntegerValuedAE P X := by
  let Y : Ω → ℂ :=
    fun ω => Complex.exp (Complex.I * (X ω : ℂ) * ((2 * Real.pi : ℝ) : ℂ))
  have hYnorm_all : ∀ ω, ‖Y ω‖ = 1 := by
    intro ω
    exact characteristic_integrand_two_pi_norm X ω
  have hYint : Integrable Y P := by
    exact (integrable_const (1 : ℂ)).mono (by fun_prop) (by
      filter_upwards with ω
      simp [hYnorm_all ω])
  constructor
  · intro hφ
    have hYintegral : ∫ ω, Y ω ∂P = 1 := by
      simpa [Y, characteristicFunction] using hφ
    have hYae : Y =ᵐ[P] fun _ => (1 : ℂ) :=
      complex_unit_integral_eq_one_ae hYint
        (Filter.Eventually.of_forall hYnorm_all) hYintegral
    filter_upwards [hYae] with ω hω
    exact (exp_two_pi_I_eq_one_iff_integerRange (X ω)).mp (by
      simpa [Y] using hω)
  · intro hInt
    have hYae : Y =ᵐ[P] fun _ => (1 : ℂ) := by
      filter_upwards [hInt] with ω hω
      exact (exp_two_pi_I_eq_one_iff_integerRange (X ω)).mpr hω
    calc
      characteristicFunction P X (2 * Real.pi) = ∫ ω, Y ω ∂P := by
        rfl
      _ = ∫ _ω : Ω, (1 : ℂ) ∂P := integral_congr_ae hYae
      _ = 1 := by
        simp

theorem prob_9_8
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P) :
    characteristicFunction P X (2 * Real.pi) = 1 ↔
      P {ω | X ω ∈ integerRange} = 1 := by
  have hnull :
      NullMeasurableSet {ω | X ω ∈ integerRange} P :=
    hX.nullMeasurableSet_preimage measurableSet_integerRange
  rw [← MeasureTheory.mem_ae_iff_prob_eq_one₀ hnull]
  exact characteristicFunction_two_pi_eq_one_iff_integerValuedAE hX
