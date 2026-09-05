/-
TASK ID: thm_11_1
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-bounds-inequalities
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace



theorem thm_11_1 {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (X Y : E) :
    ‖⟪X, Y⟫_𝕜‖ ≤ ‖X‖ * ‖Y‖ := by
  exact norm_inner_le_norm X Y



theorem thm_11_1_equality_iff {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {X Y : E} (hX : X ≠ 0) (hY : Y ≠ 0) :
    ‖⟪X, Y⟫_𝕜‖ = ‖X‖ * ‖Y‖ ↔ ∃ c : 𝕜, c ≠ 0 ∧ Y = c • X := by
  exact norm_inner_eq_norm_iff hX hY



theorem thm_11_1_equality_zero {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (Y : E) :
    ‖⟪(0 : E), Y⟫_𝕜‖ = ‖(0 : E)‖ * ‖Y‖ := by
  simp

 
theorem thm_11_1_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X Y : E) : |⟪X, Y⟫_ℝ| ≤ ‖X‖ * ‖Y‖ := by
  exact abs_real_inner_le_norm X Y

 



theorem thm_11_1_integrable_conj_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℂ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => conj (X ω) * Y ω) μ := by
  refine (MeasureTheory.L2.integrable_inner (hX.toLp X) (hY.toLp Y)).congr ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω hXω hYω
  simp [hXω, hYω, RCLike.inner_apply, mul_comm]



theorem thm_11_1_inner_toLp_eq_expectation {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℂ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ⟪hX.toLp X, hY.toLp Y⟫_ℂ = ∫ ω, conj (X ω) * Y ω ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with ω hXω hYω
  simp [hXω, hYω, RCLike.inner_apply, mul_comm]



theorem thm_11_1_sqrt_expectation_norm_sq_eq_norm_toLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℂ} (hX : MemLp X 2 μ) :
    Real.sqrt (∫ ω, ‖X ω‖ ^ 2 ∂μ) = ‖hX.toLp X‖ := by
  have hsq : ‖hX.toLp X‖ ^ 2 = ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
    calc
      ‖hX.toLp X‖ ^ 2 = RCLike.re ⟪hX.toLp X, hX.toLp X⟫_ℂ :=
        norm_sq_eq_re_inner _
      _ = RCLike.re (∫ ω, conj (X ω) * X ω ∂μ) := by
        rw [thm_11_1_inner_toLp_eq_expectation hX hX]
      _ = ∫ ω, RCLike.re (conj (X ω) * X ω) ∂μ :=
        (integral_re (thm_11_1_integrable_conj_mul hX hX)).symm
      _ = ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_conj_mul_self]
        norm_num
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]



theorem thm_11_1_expectation_complex {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℂ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ‖∫ ω, conj (X ω) * Y ω ∂μ‖ ≤
      Real.sqrt (∫ ω, ‖X ω‖ ^ 2 ∂μ) *
        Real.sqrt (∫ ω, ‖Y ω‖ ^ 2 ∂μ) := by
  rw [thm_11_1_sqrt_expectation_norm_sq_eq_norm_toLp hX,
    thm_11_1_sqrt_expectation_norm_sq_eq_norm_toLp hY]
  rw [← thm_11_1_inner_toLp_eq_expectation hX hY]
  exact thm_11_1 (hX.toLp X) (hY.toLp Y)



theorem thm_11_1_expectation_complex_equality_iff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℂ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    ‖∫ ω, conj (X ω) * Y ω ∂μ‖ =
        Real.sqrt (∫ ω, ‖X ω‖ ^ 2 ∂μ) *
          Real.sqrt (∫ ω, ‖Y ω‖ ^ 2 ∂μ) ↔
      (∃ c : ℂ, Y =ᵐ[μ] fun ω => c * X ω) ∨
        ∃ c : ℂ, X =ᵐ[μ] fun ω => c * Y ω := by
  rw [thm_11_1_sqrt_expectation_norm_sq_eq_norm_toLp hX,
    thm_11_1_sqrt_expectation_norm_sq_eq_norm_toLp hY]
  rw [← thm_11_1_inner_toLp_eq_expectation hX hY]
  constructor
  · intro heq
    by_cases hX0 : hX.toLp X = 0
    · right
      refine ⟨0, ?_⟩
      have hzero : MemLp (0 : Ω → ℂ) 2 μ := MemLp.zero
      have hXae : X =ᵐ[μ] (0 : Ω → ℂ) :=
        (hX.toLp_eq_toLp_iff hzero).mp (by simpa using hX0)
      filter_upwards [hXae] with ω hXω
      simpa using hXω
    · by_cases hY0 : hY.toLp Y = 0
      · left
        refine ⟨0, ?_⟩
        have hzero : MemLp (0 : Ω → ℂ) 2 μ := MemLp.zero
        have hYae : Y =ᵐ[μ] (0 : Ω → ℂ) :=
          (hY.toLp_eq_toLp_iff hzero).mp (by simpa using hY0)
        filter_upwards [hYae] with ω hYω
        simpa using hYω
      · rcases (thm_11_1_equality_iff hX0 hY0).mp heq with ⟨c, -, hc⟩
        left
        refine ⟨c, ?_⟩
        have htoLp :
            hY.toLp Y = (hX.const_smul c).toLp (c • X) := by
          rw [MemLp.toLp_const_smul]
          exact hc
        have hae := (hY.toLp_eq_toLp_iff (hX.const_smul c)).mp htoLp
        filter_upwards [hae] with ω hω
        simpa [Pi.smul_apply] using hω
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · have htoLp : hY.toLp Y = c • hX.toLp X := by
        rw [← hX.toLp_const_smul c]
        apply (hY.toLp_eq_toLp_iff (hX.const_smul c)).mpr
        filter_upwards [hc] with ω hω
        simpa [Pi.smul_apply] using hω
      rw [htoLp]
      simp [inner_smul_right, norm_smul, inner_self_eq_norm_sq_to_K,
        sq, mul_left_comm]
    · have htoLp : hX.toLp X = c • hY.toLp Y := by
        rw [← hY.toLp_const_smul c]
        apply (hX.toLp_eq_toLp_iff (hY.const_smul c)).mpr
        filter_upwards [hc] with ω hω
        simpa [Pi.smul_apply] using hω
      rw [htoLp]
      simp [inner_smul_left, norm_smul, inner_self_eq_norm_sq_to_K,
        sq, mul_left_comm]
      ring






theorem thm_11_1_integrable_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Integrable (fun ω => X ω * Y ω) μ :=
  hX.integrable_mul hY



theorem thm_11_1_quadratic_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (t : ℝ) :
    0 ≤ (∫ ω, X ω ^ 2 ∂μ) * (t * t)
        + (2 * ∫ ω, X ω * Y ω ∂μ) * t + (∫ ω, Y ω ^ 2 ∂μ) := by
  have hX2 : Integrable (fun ω => X ω ^ 2) μ :=
    (hX.integrable_mul hX).congr (by filter_upwards with ω; simp [Pi.mul_apply, pow_two])
  have hY2 : Integrable (fun ω => Y ω ^ 2) μ :=
    (hY.integrable_mul hY).congr (by filter_upwards with ω; simp [Pi.mul_apply, pow_two])
  have hXY : Integrable (fun ω => X ω * Y ω) μ := hX.integrable_mul hY
  have hnn : 0 ≤ ∫ ω, (t * X ω + Y ω) ^ 2 ∂μ :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hexp : (∫ ω, (t * X ω + Y ω) ^ 2 ∂μ)
      = (∫ ω, X ω ^ 2 ∂μ) * (t * t)
        + (2 * ∫ ω, X ω * Y ω ∂μ) * t + (∫ ω, Y ω ^ 2 ∂μ) := by
    have hpt : (fun ω => (t * X ω + Y ω) ^ 2)
        = (fun ω => (t * t) * X ω ^ 2 + (2 * t) * (X ω * Y ω) + Y ω ^ 2) := by
      funext ω; ring
    have e1 : Integrable (fun ω => (t * t) * X ω ^ 2) μ := hX2.const_mul _
    have e2 : Integrable (fun ω => (2 * t) * (X ω * Y ω)) μ := hXY.const_mul _
    have e12 : Integrable
        (fun ω => (t * t) * X ω ^ 2 + (2 * t) * (X ω * Y ω)) μ := e1.add e2
    rw [hpt, integral_add e12 hY2, integral_add e1 e2,
      integral_const_mul, integral_const_mul]
    ring
  rw [hexp] at hnn
  exact hnn



theorem thm_11_1_expectation {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |∫ ω, X ω * Y ω ∂μ|
      ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂μ) * Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) := by
  have ha : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg (fun ω => sq_nonneg _)
  have hd : discrim (∫ ω, X ω ^ 2 ∂μ) (2 * ∫ ω, X ω * Y ω ∂μ) (∫ ω, Y ω ^ 2 ∂μ) ≤ 0 :=
    discrim_le_zero (thm_11_1_quadratic_nonneg hX hY)
  have hsq : (∫ ω, X ω * Y ω ∂μ) ^ 2
      ≤ (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) := by
    have hdd : (2 * ∫ ω, X ω * Y ω ∂μ) ^ 2
        - 4 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, Y ω ^ 2 ∂μ) ≤ 0 := by
      simpa [discrim] using hd
    nlinarith [hdd]
  rw [← Real.sqrt_mul ha, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq
