/-
TASK ID: ex_12_4_2
TYPE: Example_Proof
SOURCE PLAN: chapter12-mmse-estimation
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.def_12_2
import ProbabilityTheory.chapter_09.def_9_1
import ProbabilityTheory.chapter_07.thm_7_13




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

open scoped InnerProductSpace BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

 
def ex_12_4_2_observed (c : ℝ) (X N : Ω →₂[P] ℝ) : Ω →₂[P] ℝ :=
  c • X + N

 
def ex_12_4_2_observedRaw (c : ℝ) (X N : Ω → ℝ) : Ω → ℝ :=
  fun ω => c * X ω + N ω

 
def ex_12_4_2_mean (X : Ω → ℝ) (_hX : L2Function P X) : ℝ :=
  P[X]

 
def ex_12_4_2_variance [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hXm : Measurable X) (hX : L2Function P X) : ℝ :=
  _root_.variance P X
    (FiniteAbsMoment.of_memLp hXm (show MemLp X (2 : ENNReal) P from hX))

 
def ex_12_4_2_secondMoment (X : Ω → ℝ) (hX : L2Function P X) : ℝ :=
  l2Inner P X X hX hX



def ex_12_4_2_actualMSE (c : ℝ) (X N : Ω → ℝ)
    (_hX : L2Function P X) (_hN : L2Function P N) (k : ℝ) : ℝ :=
  P[fun ω => (k * ex_12_4_2_observedRaw c X N ω - X ω) ^ 2]



def ex_12_4_2_quadraticMSE (EYY EXY EXX k : ℝ) : ℝ :=
  k ^ 2 * EYY - 2 * k * EXY + EXX

 
def ex_12_4_2_optimalK (EYY EXY : ℝ) : ℝ :=
  EXY / EYY



def ex_12_4_2_linearOptimalK (c mu sigmaX2 sigmaN2 : ℝ) : ℝ :=
  c * (sigmaX2 + mu ^ 2) /
    (c ^ 2 * (sigmaX2 + mu ^ 2) + sigmaN2)

 
def ex_12_4_2_sourceK (c sigmaX2 sigmaN2 : ℝ) : ℝ :=
  c * sigmaX2 / (c ^ 2 * sigmaX2 + sigmaN2)

 
def ex_12_4_2_shrinkage (c sigmaX2 sigmaN2 : ℝ) : ℝ :=
  c ^ 2 * sigmaX2 / (c ^ 2 * sigmaX2 + sigmaN2)

 
def ex_12_4_2_mmseEstimate (c sigmaX2 sigmaN2 : ℝ) (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => ex_12_4_2_sourceK c sigmaX2 sigmaN2 * Y ω

 
def ex_12_4_2_unbiasedEstimate (c : ℝ) (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => Y ω / c



theorem ex_12_4_2_quadraticMSE_sub_min
    (EYY EXY EXX k : ℝ) (hEYY : EYY ≠ 0) :
    ex_12_4_2_quadraticMSE EYY EXY EXX k -
        ex_12_4_2_quadraticMSE EYY EXY EXX (ex_12_4_2_optimalK EYY EXY) =
      EYY * (k - ex_12_4_2_optimalK EYY EXY) ^ 2 := by
  unfold ex_12_4_2_quadraticMSE ex_12_4_2_optimalK
  field_simp [hEYY]
  ring

theorem ex_12_4_2_quadraticMSE_minimal
    (EYY EXY EXX k : ℝ) (hEYY : 0 < EYY) :
    0 ≤
      ex_12_4_2_quadraticMSE EYY EXY EXX k -
        ex_12_4_2_quadraticMSE EYY EXY EXX (ex_12_4_2_optimalK EYY EXY) := by
  rw [ex_12_4_2_quadraticMSE_sub_min EYY EXY EXX k hEYY.ne']
  exact mul_nonneg hEYY.le (sq_nonneg _)

 
theorem ex_12_4_2_observedRaw_memLp
    (c : ℝ) {X N : Ω → ℝ}
    (hXL2 : L2Function P X) (hNL2 : L2Function P N) :
    L2Function P (ex_12_4_2_observedRaw c X N) := by
  change MemLp (fun ω => c * X ω + N ω) (2 : ENNReal) P
  exact
    ((show MemLp X (2 : ENNReal) P from hXL2).const_mul c).add
      (show MemLp N (2 : ENNReal) P from hNL2)

 
theorem ex_12_4_2_unbiasedEstimate_memLp
    (c : ℝ) {Y : Ω → ℝ} (hYL2 : L2Function P Y) :
    L2Function P (ex_12_4_2_unbiasedEstimate c Y) := by
  change MemLp (fun ω => Y ω / c) (2 : ENNReal) P
  simpa [div_eq_mul_inv, mul_comm] using
    (show MemLp Y (2 : ENNReal) P from hYL2).const_mul c⁻¹

 
theorem ex_12_4_2_secondMoment_eq_variance_add_mean_sq
    [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hXm : Measurable X) (hXL2 : L2Function P X) :
    ex_12_4_2_secondMoment (P := P) X hXL2 =
      ex_12_4_2_variance (P := P) X hXm hXL2 +
        ex_12_4_2_mean (P := P) X hXL2 ^ 2 := by
  have hXmem : MemLp X (2 : ENNReal) P := hXL2
  have hvar :
      ex_12_4_2_variance (P := P) X hXm hXL2 =
        P[X ^ 2] - P[X] ^ 2 := by
    rw [ex_12_4_2_variance, _root_.variance, rthCentralMoment]
    rw [ProbabilityTheory.centralMoment_two_eq_variance
      (μ := P) (X := X) hXmem.aemeasurable]
    exact ProbabilityTheory.variance_eq_sub hXmem
  calc
    ex_12_4_2_secondMoment (P := P) X hXL2 = P[X ^ 2] := by
      simp [ex_12_4_2_secondMoment, l2Inner, pow_two]
    _ = ex_12_4_2_variance (P := P) X hXm hXL2 +
        ex_12_4_2_mean (P := P) X hXL2 ^ 2 := by
      rw [hvar]
      unfold ex_12_4_2_mean
      ring

 
theorem ex_12_4_2_independent_noise_orthogonal [IsProbabilityMeasure P]
    {X N : Ω → ℝ}
    (hXL2 : L2Function P X) (hNL2 : L2Function P N)
    (hXN : def_5_2 P X N)
    (hN0 : ex_12_4_2_mean (P := P) N hNL2 = 0) :
    l2Inner P X N hXL2 hNL2 = 0 := by
  have hX_int : Integrable X P := hXL2.integrable
  have hN_int : Integrable N P := hNL2.integrable
  have hXN_int : Integrable (fun ω => X ω * N ω) P :=
    l2Inner_integrable hXL2 hNL2
  unfold l2Inner ex_12_4_2_mean at *
  rw [thm_7_13 hXN hX_int hN_int hXN_int, hN0, mul_zero]

 
theorem ex_12_4_2_unbiasedEstimate_mean
    [IsProbabilityMeasure P] (c mu : ℝ) {X N : Ω → ℝ}
    (hXL2 : L2Function P X) (hNL2 : L2Function P N)
    (hXmean : ex_12_4_2_mean (P := P) X hXL2 = mu)
    (hN0 : ex_12_4_2_mean (P := P) N hNL2 = 0) (hc : c ≠ 0) :
    ex_12_4_2_mean (P := P)
        (ex_12_4_2_unbiasedEstimate c (ex_12_4_2_observedRaw c X N))
        (ex_12_4_2_unbiasedEstimate_memLp (P := P) c
          (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2)) = mu := by
  have hX_int : Integrable X P := hXL2.integrable
  have hN_int : Integrable N P := hNL2.integrable
  unfold ex_12_4_2_mean ex_12_4_2_unbiasedEstimate ex_12_4_2_observedRaw at *
  rw [integral_div, integral_add (hX_int.const_mul c) hN_int,
    integral_const_mul, hXmean, hN0]
  field_simp [hc]
  simp



theorem ex_12_4_2_actualMSE_eq_quadraticMSE
    (c k : ℝ) {X N : Ω → ℝ}
    (hXL2 : L2Function P X) (hNL2 : L2Function P N) :
    ex_12_4_2_actualMSE (P := P) c X N hXL2 hNL2 k =
      ex_12_4_2_quadraticMSE
        (ex_12_4_2_secondMoment (P := P)
          (ex_12_4_2_observedRaw c X N)
          (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2))
        (l2Inner P X (ex_12_4_2_observedRaw c X N) hXL2
          (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2))
        (ex_12_4_2_secondMoment (P := P) X hXL2) k := by
  have hYL2 : L2Function P (ex_12_4_2_observedRaw c X N) :=
    ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2
  have hYY :
      Integrable (fun ω =>
        ex_12_4_2_observedRaw c X N ω * ex_12_4_2_observedRaw c X N ω) P :=
    l2Inner_integrable hYL2 hYL2
  have hXY :
      Integrable (fun ω => X ω * ex_12_4_2_observedRaw c X N ω) P :=
    l2Inner_integrable hXL2 hYL2
  have hXX : Integrable (fun ω => X ω * X ω) P :=
    l2Inner_integrable hXL2 hXL2
  have hkYY :
      Integrable (fun ω =>
        k ^ 2 * (ex_12_4_2_observedRaw c X N ω *
          ex_12_4_2_observedRaw c X N ω)) P :=
    hYY.const_mul (k ^ 2)
  have hkXY :
      Integrable (fun ω =>
        (2 * k) * (X ω * ex_12_4_2_observedRaw c X N ω)) P :=
    hXY.const_mul (2 * k)
  unfold ex_12_4_2_actualMSE ex_12_4_2_quadraticMSE
    ex_12_4_2_secondMoment l2Inner
  calc
    (P[fun ω =>
        (k * ex_12_4_2_observedRaw c X N ω - X ω) ^ 2]) =
        P[fun ω =>
          k ^ 2 * (ex_12_4_2_observedRaw c X N ω *
            ex_12_4_2_observedRaw c X N ω) -
          (2 * k) * (X ω * ex_12_4_2_observedRaw c X N ω) +
          X ω * X ω] := by
      congr with ω
      ring
    _ = P[fun ω =>
          k ^ 2 * (ex_12_4_2_observedRaw c X N ω *
            ex_12_4_2_observedRaw c X N ω) -
          (2 * k) * (X ω * ex_12_4_2_observedRaw c X N ω)] +
        P[fun ω => X ω * X ω] := by
      rw [integral_add
        (f := fun ω =>
          k ^ 2 * (ex_12_4_2_observedRaw c X N ω *
            ex_12_4_2_observedRaw c X N ω) -
          (2 * k) * (X ω * ex_12_4_2_observedRaw c X N ω))
        (g := fun ω => X ω * X ω) (hkYY.sub hkXY) hXX]
    _ = (P[fun ω =>
          k ^ 2 * (ex_12_4_2_observedRaw c X N ω *
            ex_12_4_2_observedRaw c X N ω)] -
        P[fun ω =>
          (2 * k) * (X ω * ex_12_4_2_observedRaw c X N ω)]) +
        P[fun ω => X ω * X ω] := by
      rw [integral_sub
        (f := fun ω =>
          k ^ 2 * (ex_12_4_2_observedRaw c X N ω *
            ex_12_4_2_observedRaw c X N ω))
        (g := fun ω =>
          (2 * k) * (X ω * ex_12_4_2_observedRaw c X N ω)) hkYY hkXY]
    _ = k ^ 2 * P[fun ω =>
          ex_12_4_2_observedRaw c X N ω * ex_12_4_2_observedRaw c X N ω] -
        2 * k * P[fun ω => X ω * ex_12_4_2_observedRaw c X N ω] +
        P[fun ω => X ω * X ω] := by
      rw [integral_const_mul, integral_const_mul]

 
theorem ex_12_4_2_crossMoment_observedRaw
    (c EXX : ℝ) {X N : Ω → ℝ}
    (hXL2 : L2Function P X) (hNL2 : L2Function P N)
    (hXN0 : l2Inner P X N hXL2 hNL2 = 0)
    (hXX : ex_12_4_2_secondMoment (P := P) X hXL2 = EXX) :
    l2Inner P X (ex_12_4_2_observedRaw c X N) hXL2
        (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2) = c * EXX := by
  have hXXint : Integrable (fun ω => X ω * X ω) P :=
    l2Inner_integrable hXL2 hXL2
  have hXNint : Integrable (fun ω => X ω * N ω) P :=
    l2Inner_integrable hXL2 hNL2
  unfold ex_12_4_2_secondMoment l2Inner at hXX
  unfold l2Inner at hXN0 ⊢
  change (P[fun ω => X ω * (c * X ω + N ω)]) = c * EXX
  calc
    (P[fun ω => X ω * (c * X ω + N ω)]) =
        P[fun ω => c * (X ω * X ω) + X ω * N ω] := by
      congr with ω
      ring
    _ = c * P[fun ω => X ω * X ω] + P[fun ω => X ω * N ω] := by
      rw [integral_add (hXXint.const_mul c) hXNint, integral_const_mul]
    _ = c * EXX := by
      rw [hXX, hXN0]
      ring

 
theorem ex_12_4_2_observedRaw_secondMoment
    (c EXX ENN : ℝ) {X N : Ω → ℝ}
    (hXL2 : L2Function P X) (hNL2 : L2Function P N)
    (hXN0 : l2Inner P X N hXL2 hNL2 = 0)
    (hXX : ex_12_4_2_secondMoment (P := P) X hXL2 = EXX)
    (hNN : ex_12_4_2_secondMoment (P := P) N hNL2 = ENN) :
    ex_12_4_2_secondMoment (P := P) (ex_12_4_2_observedRaw c X N)
        (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2) =
      c ^ 2 * EXX + ENN := by
  have hXXint : Integrable (fun ω => X ω * X ω) P :=
    l2Inner_integrable hXL2 hXL2
  have hXNint : Integrable (fun ω => X ω * N ω) P :=
    l2Inner_integrable hXL2 hNL2
  have hNNint : Integrable (fun ω => N ω * N ω) P :=
    l2Inner_integrable hNL2 hNL2
  unfold ex_12_4_2_secondMoment at hXX hNN ⊢
  unfold l2Inner at hXX hNN hXN0 ⊢
  change (P[fun ω => (c * X ω + N ω) * (c * X ω + N ω)]) =
    c ^ 2 * EXX + ENN
  calc
    (P[fun ω => (c * X ω + N ω) * (c * X ω + N ω)]) =
        P[fun ω =>
          c ^ 2 * (X ω * X ω) + (2 * c) * (X ω * N ω) + N ω * N ω] := by
      congr with ω
      ring
    _ = P[fun ω =>
          c ^ 2 * (X ω * X ω) + (2 * c) * (X ω * N ω)] +
        P[fun ω => N ω * N ω] := by
      rw [integral_add
        (f := fun ω =>
          c ^ 2 * (X ω * X ω) + (2 * c) * (X ω * N ω))
        (g := fun ω => N ω * N ω)
        ((hXXint.const_mul (c ^ 2)).add (hXNint.const_mul (2 * c))) hNNint]
    _ = (P[fun ω => c ^ 2 * (X ω * X ω)] +
        P[fun ω => (2 * c) * (X ω * N ω)]) +
        P[fun ω => N ω * N ω] := by
      rw [integral_add
        (f := fun ω => c ^ 2 * (X ω * X ω))
        (g := fun ω => (2 * c) * (X ω * N ω))
        (hXXint.const_mul (c ^ 2)) (hXNint.const_mul (2 * c))]
    _ = c ^ 2 * P[fun ω => X ω * X ω] +
        (2 * c) * P[fun ω => X ω * N ω] +
        P[fun ω => N ω * N ω] := by
      rw [integral_const_mul, integral_const_mul]
    _ = c ^ 2 * EXX + ENN := by
      rw [hXX, hXN0, hNN]
      ring



theorem ex_12_4_2_toLp_inner_eq_l2Inner {X N : Ω → ℝ}
    (hXL2 : L2Function P X) (hNL2 : L2Function P N) :
    ⟪L2Function.toLp hXL2, L2Function.toLp hNL2⟫_ℝ =
      l2Inner P X N hXL2 hNL2 := by
  rw [L2.inner_def]
  unfold l2Inner L2Function.toLp
  apply integral_congr_ae
  have hXae := MemLp.coeFn_toLp (show MemLp X (2 : ENNReal) P from hXL2)
  have hNae := MemLp.coeFn_toLp (show MemLp N (2 : ENNReal) P from hNL2)
  filter_upwards [hXae, hNae] with ω hXω hNω
  rw [hXω, hNω]
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply']
  simp

 
theorem ex_12_4_2_crossMoment_observed
    (c sigmaX2 : ℝ) (X N : Ω →₂[P] ℝ)
    (hXN : ⟪X, N⟫_ℝ = 0) (hXX : ⟪X, X⟫_ℝ = sigmaX2) :
    ⟪X, ex_12_4_2_observed (P := P) c X N⟫_ℝ = c * sigmaX2 := by
  unfold ex_12_4_2_observed
  rw [inner_add_right, inner_smul_right, hXN, hXX]
  simp only [add_zero]

 
theorem ex_12_4_2_observed_secondMoment
    (c sigmaX2 sigmaN2 : ℝ) (X N : Ω →₂[P] ℝ)
    (hXN : ⟪X, N⟫_ℝ = 0) (hXX : ⟪X, X⟫_ℝ = sigmaX2)
    (hNN : ⟪N, N⟫_ℝ = sigmaN2) :
    ⟪ex_12_4_2_observed (P := P) c X N,
      ex_12_4_2_observed (P := P) c X N⟫_ℝ =
        c ^ 2 * sigmaX2 + sigmaN2 := by
  have hNX : ⟪N, X⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact hXN
  unfold ex_12_4_2_observed
  rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_right,
    inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  rw [hXN, hXX, hNN, hNX]
  ring

theorem ex_12_4_2_sourceK_eq_optimalK (c sigmaX2 sigmaN2 : ℝ) :
    ex_12_4_2_optimalK (c ^ 2 * sigmaX2 + sigmaN2) (c * sigmaX2) =
      ex_12_4_2_sourceK c sigmaX2 sigmaN2 := by
  rfl



theorem ex_12_4_2_linearOptimalK_zero (c sigmaX2 sigmaN2 : ℝ) :
    ex_12_4_2_linearOptimalK c 0 sigmaX2 sigmaN2 =
      ex_12_4_2_sourceK c sigmaX2 sigmaN2 := by
  simp [ex_12_4_2_linearOptimalK, ex_12_4_2_sourceK]



theorem ex_12_4_2_mmseEstimate_eq_shrinkage_unbiased
    (c sigmaX2 sigmaN2 : ℝ) (Y : Ω → ℝ) (hc : c ≠ 0) :
    ex_12_4_2_mmseEstimate c sigmaX2 sigmaN2 Y =
      fun ω =>
        ex_12_4_2_shrinkage c sigmaX2 sigmaN2 *
          ex_12_4_2_unbiasedEstimate c Y ω := by
  funext ω
  unfold ex_12_4_2_mmseEstimate ex_12_4_2_shrinkage ex_12_4_2_unbiasedEstimate
    ex_12_4_2_sourceK
  field_simp [hc]



theorem ex_12_4_2 [IsProbabilityMeasure P]
    (c mu sigmaX2 sigmaN2 : ℝ) {X N : Ω → ℝ}
    (hXm : Measurable X) (hNm : Measurable N)
    (hXL2 : L2Function P X) (hNL2 : L2Function P N)
    (hXN : def_5_2 P X N)
    (hXmean : ex_12_4_2_mean (P := P) X hXL2 = mu)
    (hN0 : ex_12_4_2_mean (P := P) N hNL2 = 0)
    (hXvar : ex_12_4_2_variance (P := P) X hXm hXL2 = sigmaX2)
    (hNvar : ex_12_4_2_variance (P := P) N hNm hNL2 = sigmaN2)
    (hc : c ≠ 0)
    (hden : 0 < c ^ 2 * (sigmaX2 + mu ^ 2) + sigmaN2) :
    ex_12_4_2_mean (P := P)
        (ex_12_4_2_unbiasedEstimate c (ex_12_4_2_observedRaw c X N))
        (ex_12_4_2_unbiasedEstimate_memLp (P := P) c
          (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2)) = mu ∧
      ex_12_4_2_secondMoment (P := P) X hXL2 = sigmaX2 + mu ^ 2 ∧
      ex_12_4_2_secondMoment (P := P) N hNL2 = sigmaN2 ∧
      l2Inner P X (ex_12_4_2_observedRaw c X N) hXL2
          (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2) =
        c * (sigmaX2 + mu ^ 2) ∧
      ex_12_4_2_secondMoment (P := P) (ex_12_4_2_observedRaw c X N)
          (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2) =
        c ^ 2 * (sigmaX2 + mu ^ 2) + sigmaN2 ∧
      (∀ k : ℝ,
        ex_12_4_2_actualMSE (P := P) c X N hXL2 hNL2 k =
          ex_12_4_2_quadraticMSE
            (c ^ 2 * (sigmaX2 + mu ^ 2) + sigmaN2)
            (c * (sigmaX2 + mu ^ 2)) (sigmaX2 + mu ^ 2) k) ∧
      ex_12_4_2_optimalK
          (c ^ 2 * (sigmaX2 + mu ^ 2) + sigmaN2)
          (c * (sigmaX2 + mu ^ 2)) =
        ex_12_4_2_linearOptimalK c mu sigmaX2 sigmaN2 ∧
      (∀ k : ℝ,
        0 ≤ ex_12_4_2_actualMSE (P := P) c X N hXL2 hNL2 k -
          ex_12_4_2_actualMSE (P := P) c X N hXL2 hNL2
            (ex_12_4_2_linearOptimalK c mu sigmaX2 sigmaN2)) ∧
      (mu = 0 →
        ex_12_4_2_linearOptimalK c mu sigmaX2 sigmaN2 =
            ex_12_4_2_sourceK c sigmaX2 sigmaN2 ∧
          ex_12_4_2_mmseEstimate c sigmaX2 sigmaN2
              (ex_12_4_2_observedRaw c X N) =
            fun ω =>
              ex_12_4_2_shrinkage c sigmaX2 sigmaN2 *
                ex_12_4_2_unbiasedEstimate c
                  (ex_12_4_2_observedRaw c X N) ω) := by
  have hXX :
      ex_12_4_2_secondMoment (P := P) X hXL2 = sigmaX2 + mu ^ 2 := by
    rw [ex_12_4_2_secondMoment_eq_variance_add_mean_sq (P := P) hXm hXL2,
      hXvar, hXmean]
  have hNN :
      ex_12_4_2_secondMoment (P := P) N hNL2 = sigmaN2 := by
    rw [ex_12_4_2_secondMoment_eq_variance_add_mean_sq (P := P) hNm hNL2,
      hNvar, hN0]
    ring
  have hOrth : l2Inner P X N hXL2 hNL2 = 0 :=
    ex_12_4_2_independent_noise_orthogonal (P := P) hXL2 hNL2 hXN hN0
  have hCross :
      l2Inner P X (ex_12_4_2_observedRaw c X N) hXL2
          (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2) =
        c * (sigmaX2 + mu ^ 2) :=
    ex_12_4_2_crossMoment_observedRaw (P := P) c (sigmaX2 + mu ^ 2)
      hXL2 hNL2 hOrth hXX
  have hObserved :
      ex_12_4_2_secondMoment (P := P) (ex_12_4_2_observedRaw c X N)
          (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2) =
        c ^ 2 * (sigmaX2 + mu ^ 2) + sigmaN2 :=
    ex_12_4_2_observedRaw_secondMoment (P := P) c
      (sigmaX2 + mu ^ 2) sigmaN2 hXL2 hNL2 hOrth hXX hNN
  have hUnbiased :
      ex_12_4_2_mean (P := P)
          (ex_12_4_2_unbiasedEstimate c (ex_12_4_2_observedRaw c X N))
          (ex_12_4_2_unbiasedEstimate_memLp (P := P) c
            (ex_12_4_2_observedRaw_memLp (P := P) c hXL2 hNL2)) = mu :=
    ex_12_4_2_unbiasedEstimate_mean (P := P) c mu hXL2 hNL2 hXmean hN0 hc
  have hMSE : ∀ k : ℝ,
      ex_12_4_2_actualMSE (P := P) c X N hXL2 hNL2 k =
        ex_12_4_2_quadraticMSE
          (c ^ 2 * (sigmaX2 + mu ^ 2) + sigmaN2)
          (c * (sigmaX2 + mu ^ 2)) (sigmaX2 + mu ^ 2) k := by
    intro k
    rw [ex_12_4_2_actualMSE_eq_quadraticMSE (P := P) c k hXL2 hNL2,
      hObserved, hCross, hXX]
  have hOptimal :
      ex_12_4_2_optimalK
          (c ^ 2 * (sigmaX2 + mu ^ 2) + sigmaN2)
          (c * (sigmaX2 + mu ^ 2)) =
        ex_12_4_2_linearOptimalK c mu sigmaX2 sigmaN2 := by
    rfl
  have hMinimal : ∀ k : ℝ,
      0 ≤ ex_12_4_2_actualMSE (P := P) c X N hXL2 hNL2 k -
        ex_12_4_2_actualMSE (P := P) c X N hXL2 hNL2
          (ex_12_4_2_linearOptimalK c mu sigmaX2 sigmaN2) := by
    intro k
    rw [← hOptimal]
    rw [hMSE k,
      hMSE (ex_12_4_2_optimalK
        (c ^ 2 * (sigmaX2 + mu ^ 2) + sigmaN2)
        (c * (sigmaX2 + mu ^ 2)))]
    exact
      ex_12_4_2_quadraticMSE_minimal
        (c ^ 2 * (sigmaX2 + mu ^ 2) + sigmaN2)
        (c * (sigmaX2 + mu ^ 2)) (sigmaX2 + mu ^ 2) k hden
  have hCentered : mu = 0 →
      ex_12_4_2_linearOptimalK c mu sigmaX2 sigmaN2 =
          ex_12_4_2_sourceK c sigmaX2 sigmaN2 ∧
        ex_12_4_2_mmseEstimate c sigmaX2 sigmaN2
            (ex_12_4_2_observedRaw c X N) =
          fun ω =>
            ex_12_4_2_shrinkage c sigmaX2 sigmaN2 *
              ex_12_4_2_unbiasedEstimate c
                (ex_12_4_2_observedRaw c X N) ω := by
    intro hmu0
    constructor
    · simpa [hmu0] using
        ex_12_4_2_linearOptimalK_zero c sigmaX2 sigmaN2
    · exact ex_12_4_2_mmseEstimate_eq_shrinkage_unbiased c sigmaX2 sigmaN2
        (ex_12_4_2_observedRaw c X N) hc
  exact ⟨hUnbiased, hXX, hNN, hCross, hObserved, hMSE, hOptimal, hMinimal, hCentered⟩
