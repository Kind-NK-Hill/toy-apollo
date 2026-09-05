/-
TASK ID: thm_12_1
TYPE: Theorem_Statement
SOURCE PLAN: chapter12-l2-norm-inner-product
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_12.def_12_2




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace

 
theorem thm_12_1_inner_add_smul {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (X Y1 Y2 : E) (α β : 𝕜) :
    ⟪X, α • Y1 + β • Y2⟫_𝕜 =
      α * ⟪X, Y1⟫_𝕜 + β * ⟪X, Y2⟫_𝕜 := by
  calc
    ⟪X, α • Y1 + β • Y2⟫_𝕜 =
        ⟪X, α • Y1⟫_𝕜 + ⟪X, β • Y2⟫_𝕜 := by
      rw [inner_add_right]
    _ = α * ⟪X, Y1⟫_𝕜 + β * ⟪X, Y2⟫_𝕜 := by
      rw [inner_smul_right, inner_smul_right]

 
theorem thm_12_1_real_symm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X Y : E) :
    ⟪X, Y⟫_ℝ = ⟪Y, X⟫_ℝ := by
  exact (real_inner_comm X Y).symm

 
theorem thm_12_1_conj_symm {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (X Y : E) :
    ⟪X, Y⟫_𝕜 = star ⟪Y, X⟫_𝕜 := by
  exact (inner_conj_symm X Y).symm

 
theorem thm_12_1_norm_smul {𝕜 E : Type*} [Norm 𝕜]
    [NormedAddCommGroup E] [SMul 𝕜 E] [NormSMulClass 𝕜 E]
    (α : 𝕜) (X : E) :
    ‖α • X‖ = ‖α‖ * ‖X‖ := by
  exact norm_smul α X

 
theorem thm_12_1_triangle {E : Type*} [NormedAddCommGroup E] (X Y : E) :
    ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := by
  exact norm_add_le X Y

 
theorem thm_12_1_innerProductSpace {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (X Y Y1 Y2 : E) (α β : 𝕜) :
    ⟪X, α • Y1 + β • Y2⟫_𝕜 =
        α * ⟪X, Y1⟫_𝕜 + β * ⟪X, Y2⟫_𝕜 ∧
      ⟪X, Y⟫_𝕜 = star ⟪Y, X⟫_𝕜 ∧
      ‖α • X‖ = ‖α‖ * ‖X‖ ∧
      ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := by
  exact ⟨thm_12_1_inner_add_smul X Y1 Y2 α β,
    thm_12_1_conj_symm X Y, thm_12_1_norm_smul α X,
    thm_12_1_triangle X Y⟩

namespace L2Function



theorem coeFn_toLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : L2Function P X) :
    (L2Function.toLp hX : Ω → ℝ) =ᵐ[P] X := by
  unfold L2Function.toLp
  exact MemLp.coeFn_toLp (show MemLp X (2 : ENNReal) P from hX)

 
theorem const_smul_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : L2Function P X) (α : ℝ) :
    L2Function P (α • X) :=
  (show MemLp X (2 : ENNReal) P from hX).const_smul α

 
theorem add_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} (hX : L2Function P X) (hY : L2Function P Y) :
    L2Function P (X + Y) :=
  (show MemLp X (2 : ENNReal) P from hX).add
    (show MemLp Y (2 : ENNReal) P from hY)



theorem linearCombination_mem {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y1 Y2 : Ω → ℝ}
    (hY1 : L2Function P Y1) (hY2 : L2Function P Y2) (α β : ℝ) :
    L2Function P (α • Y1 + β • Y2) :=
  ((show MemLp Y1 (2 : ENNReal) P from hY1).const_smul α).add
    ((show MemLp Y2 (2 : ENNReal) P from hY2).const_smul β)



theorem toLp_const_smul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} (hX : L2Function P X) (α : ℝ)
    (hαX : L2Function P (α • X)) :
    L2Function.toLp hαX = α • L2Function.toLp hX := by
  unfold L2Function.toLp
  simpa only using
    (MemLp.toLp_const_smul (p := (2 : ENNReal)) α
      (show MemLp X (2 : ENNReal) P from hX))



theorem toLp_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} (hX : L2Function P X) (hY : L2Function P Y)
    (hXY : L2Function P (X + Y)) :
    L2Function.toLp hXY = L2Function.toLp hX + L2Function.toLp hY := by
  unfold L2Function.toLp
  simpa only using
    (MemLp.toLp_add (show MemLp X (2 : ENNReal) P from hX)
      (show MemLp Y (2 : ENNReal) P from hY))



theorem toLp_linearCombination {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y1 Y2 : Ω → ℝ}
    (hY1 : L2Function P Y1) (hY2 : L2Function P Y2) (α β : ℝ)
    (hlin : L2Function P (α • Y1 + β • Y2)) :
    L2Function.toLp hlin =
      α • L2Function.toLp hY1 + β • L2Function.toLp hY2 := by
  unfold L2Function.toLp
  have hadd :=
    MemLp.toLp_add
      ((show MemLp Y1 (2 : ENNReal) P from hY1).const_smul α)
      ((show MemLp Y2 (2 : ENNReal) P from hY2).const_smul β)
  rw [
    MemLp.toLp_const_smul (p := (2 : ENNReal)) α
      (show MemLp Y1 (2 : ENNReal) P from hY1),
    MemLp.toLp_const_smul (p := (2 : ENNReal)) β
      (show MemLp Y2 (2 : ENNReal) P from hY2)
  ] at hadd
  exact hadd



theorem inner_toLp_eq_l2Inner {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function P X) (hY : L2Function P Y) :
    ⟪L2Function.toLp hX, L2Function.toLp hY⟫_ℝ =
      l2Inner P X Y hX hY := by
  rw [L2.inner_def]
  unfold l2Inner L2Function.toLp
  apply integral_congr_ae
  have hXae := MemLp.coeFn_toLp
    (show MemLp X (2 : ENNReal) P from hX)
  have hYae := MemLp.coeFn_toLp
    (show MemLp Y (2 : ENNReal) P from hY)
  filter_upwards [hXae, hYae] with ω hXω hYω
  rw [hXω, hYω]
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply']
  simp



theorem norm_toLp_eq_l2Norm {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : L2Function P X) :
    ‖L2Function.toLp hX‖ = l2Norm P X hX := by
  rw [l2Norm, ← inner_toLp_eq_l2Inner]
  rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

end L2Function

namespace ComplexL2Function



noncomputable def toLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℂ} (hX : ComplexL2Function P X) : Ω →₂[P] ℂ :=
  (show MemLp X (2 : ENNReal) P from hX).toLp X



theorem coeFn_toLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℂ} (hX : ComplexL2Function P X) :
    (ComplexL2Function.toLp hX : Ω → ℂ) =ᵐ[P] X := by
  unfold ComplexL2Function.toLp
  exact MemLp.coeFn_toLp (show MemLp X (2 : ENNReal) P from hX)



theorem const_smul_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℂ} (hX : ComplexL2Function P X) (α : ℂ) :
    ComplexL2Function P (α • X) :=
  (show MemLp X (2 : ENNReal) P from hX).const_smul α

 
theorem add_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℂ} (hX : ComplexL2Function P X)
    (hY : ComplexL2Function P Y) : ComplexL2Function P (X + Y) :=
  (show MemLp X (2 : ENNReal) P from hX).add
    (show MemLp Y (2 : ENNReal) P from hY)



theorem linearCombination_mem {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y1 Y2 : Ω → ℂ}
    (hY1 : ComplexL2Function P Y1) (hY2 : ComplexL2Function P Y2)
    (α β : ℂ) : ComplexL2Function P (α • Y1 + β • Y2) :=
  ((show MemLp Y1 (2 : ENNReal) P from hY1).const_smul α).add
    ((show MemLp Y2 (2 : ENNReal) P from hY2).const_smul β)



theorem toLp_linearCombination {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y1 Y2 : Ω → ℂ}
    (hY1 : ComplexL2Function P Y1) (hY2 : ComplexL2Function P Y2)
    (α β : ℂ) (hlin : ComplexL2Function P (α • Y1 + β • Y2)) :
    ComplexL2Function.toLp hlin =
      α • ComplexL2Function.toLp hY1 +
        β • ComplexL2Function.toLp hY2 := by
  unfold ComplexL2Function.toLp
  have hadd :=
    MemLp.toLp_add
      ((show MemLp Y1 (2 : ENNReal) P from hY1).const_smul α)
      ((show MemLp Y2 (2 : ENNReal) P from hY2).const_smul β)
  rw [
    MemLp.toLp_const_smul (p := (2 : ENNReal)) α
      (show MemLp Y1 (2 : ENNReal) P from hY1),
    MemLp.toLp_const_smul (p := (2 : ENNReal)) β
      (show MemLp Y2 (2 : ENNReal) P from hY2)
  ] at hadd
  exact hadd



theorem inner_toLp_eq_complexL2Inner {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℂ}
    (hX : ComplexL2Function P X) (hY : ComplexL2Function P Y) :
    ⟪ComplexL2Function.toLp hX, ComplexL2Function.toLp hY⟫_ℂ =
      complexL2Inner P X Y hX hY := by
  rw [L2.inner_def]
  unfold complexL2Inner ComplexL2Function.toLp
  apply integral_congr_ae
  have hXae := MemLp.coeFn_toLp
    (show MemLp X (2 : ENNReal) P from hX)
  have hYae := MemLp.coeFn_toLp
    (show MemLp Y (2 : ENNReal) P from hY)
  filter_upwards [hXae, hYae] with ω hXω hYω
  rw [hXω, hYω, RCLike.inner_apply']
  rfl

end ComplexL2Function



theorem l2Inner_proof_irrel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ)
    (hX hX' : L2Function P X) (hY hY' : L2Function P Y) :
    l2Inner P X Y hX hY = l2Inner P X Y hX' hY' := by
  rfl

 
theorem complexL2Inner_proof_irrel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℂ)
    (hX hX' : ComplexL2Function P X)
    (hY hY' : ComplexL2Function P Y) :
    complexL2Inner P X Y hX hY = complexL2Inner P X Y hX' hY' := by
  rfl

 
theorem l2Norm_proof_irrel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hX hX' : L2Function P X) :
    l2Norm P X hX = l2Norm P X hX' := by
  rfl

 
theorem l2Inner_eq_inner_toLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function P X) (hY : L2Function P Y) :
    l2Inner P X Y hX hY =
      ⟪L2Function.toLp hX, L2Function.toLp hY⟫_ℝ :=
  (L2Function.inner_toLp_eq_l2Inner hX hY).symm



theorem def_12_2_eq_inner_toLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function P X) (hY : L2Function P Y) :
    def_12_2 P X Y hX hY =
      ⟪L2Function.toLp hX, L2Function.toLp hY⟫_ℝ := by
  exact l2Inner_eq_inner_toLp hX hY



theorem complexL2Inner_eq_inner_toLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℂ}
    (hX : ComplexL2Function P X) (hY : ComplexL2Function P Y) :
    complexL2Inner P X Y hX hY =
      ⟪ComplexL2Function.toLp hX,
        ComplexL2Function.toLp hY⟫_ℂ :=
  (ComplexL2Function.inner_toLp_eq_complexL2Inner hX hY).symm

 
theorem l2Norm_eq_norm_toLp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : L2Function P X) :
    l2Norm P X hX = ‖L2Function.toLp hX‖ :=
  (L2Function.norm_toLp_eq_l2Norm hX).symm



theorem thm_12_1_l2Inner_add_smul {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y1 Y2 : Ω → ℝ}
    (hX : L2Function P X) (hY1 : L2Function P Y1)
    (hY2 : L2Function P Y2) (α β : ℝ) :
    l2Inner P X (α • Y1 + β • Y2) hX
        (L2Function.linearCombination_mem hY1 hY2 α β) =
      α * l2Inner P X Y1 hX hY1 + β * l2Inner P X Y2 hX hY2 := by
  simp only [l2Inner_eq_inner_toLp]
  rw [L2Function.toLp_linearCombination hY1 hY2 α β]
  exact thm_12_1_inner_add_smul _ _ _ α β

 
theorem thm_12_1_l2Inner_symm {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function P X) (hY : L2Function P Y) :
    l2Inner P X Y hX hY = l2Inner P Y X hY hX := by
  simp only [l2Inner_eq_inner_toLp]
  exact thm_12_1_real_symm _ _



theorem thm_12_1_complexL2Inner_add_smul {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X Y1 Y2 : Ω → ℂ}
    (hX : ComplexL2Function P X) (hY1 : ComplexL2Function P Y1)
    (hY2 : ComplexL2Function P Y2) (α β : ℂ) :
    complexL2Inner P X (α • Y1 + β • Y2) hX
        (ComplexL2Function.linearCombination_mem hY1 hY2 α β) =
      α * complexL2Inner P X Y1 hX hY1 +
        β * complexL2Inner P X Y2 hX hY2 := by
  simp only [complexL2Inner_eq_inner_toLp]
  rw [ComplexL2Function.toLp_linearCombination hY1 hY2 α β]
  exact thm_12_1_inner_add_smul _ _ _ α β

 
theorem thm_12_1_complexL2Inner_conj_symm {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℂ}
    (hX : ComplexL2Function P X) (hY : ComplexL2Function P Y) :
    complexL2Inner P X Y hX hY =
      star (complexL2Inner P Y X hY hX) := by
  simp only [complexL2Inner_eq_inner_toLp]
  exact thm_12_1_conj_symm _ _

 
theorem thm_12_1_l2Norm_smul {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : L2Function P X) (α : ℝ) :
    l2Norm P (α • X) (L2Function.const_smul_mem hX α) =
      |α| * l2Norm P X hX := by
  simp only [l2Norm_eq_norm_toLp]
  rw [L2Function.toLp_const_smul hX α]
  simpa only [Real.norm_eq_abs] using
    (thm_12_1_norm_smul α (L2Function.toLp hX))

 
theorem thm_12_1_l2Norm_add_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function P X) (hY : L2Function P Y) :
    l2Norm P (X + Y) (L2Function.add_mem hX hY) ≤
      l2Norm P X hX + l2Norm P Y hY := by
  simp only [l2Norm_eq_norm_toLp]
  rw [L2Function.toLp_add hX hY]
  exact thm_12_1_triangle _ _



theorem thm_12_1_real {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Y1 Y2 : Ω → ℝ) (hX : L2Function P X)
    (hY : L2Function P Y) (hY1 : L2Function P Y1)
    (hY2 : L2Function P Y2) (α β : ℝ) :
    l2Inner P X (α • Y1 + β • Y2) hX
        (L2Function.linearCombination_mem hY1 hY2 α β) =
        α * l2Inner P X Y1 hX hY1 + β * l2Inner P X Y2 hX hY2 ∧
      l2Inner P X Y hX hY = l2Inner P Y X hY hX ∧
      l2Norm P (α • X) (L2Function.const_smul_mem hX α) =
        |α| * l2Norm P X hX ∧
      l2Norm P (X + Y) (L2Function.add_mem hX hY) ≤
        l2Norm P X hX + l2Norm P Y hY := by
  exact ⟨thm_12_1_l2Inner_add_smul hX hY1 hY2 α β,
    thm_12_1_l2Inner_symm hX hY, thm_12_1_l2Norm_smul hX α,
    thm_12_1_l2Norm_add_le hX hY⟩



theorem thm_12_1_complex {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Y1 Y2 : Ω → ℂ) (hX : ComplexL2Function P X)
    (hY : ComplexL2Function P Y)
    (hY1 : ComplexL2Function P Y1)
    (hY2 : ComplexL2Function P Y2) (α β : ℂ) :
    complexL2Inner P X (α • Y1 + β • Y2) hX
        (ComplexL2Function.linearCombination_mem hY1 hY2 α β) =
        α * complexL2Inner P X Y1 hX hY1 +
          β * complexL2Inner P X Y2 hX hY2 ∧
      complexL2Inner P X Y hX hY =
        star (complexL2Inner P Y X hY hX) := by
  exact ⟨thm_12_1_complexL2Inner_add_smul hX hY1 hY2 α β,
    thm_12_1_complexL2Inner_conj_symm hX hY⟩



theorem thm_12_1 {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y Y1 Y2 : Ω →₂[P] 𝕜) (α β : 𝕜) :
    ⟪X, α • Y1 + β • Y2⟫_𝕜 =
        α * ⟪X, Y1⟫_𝕜 + β * ⟪X, Y2⟫_𝕜 ∧
      ⟪X, Y⟫_𝕜 = star ⟪Y, X⟫_𝕜 ∧
      ‖α • X‖ = ‖α‖ * ‖X‖ ∧
      ‖X + Y‖ ≤ ‖X‖ + ‖Y‖ := by
  exact thm_12_1_innerProductSpace X Y Y1 Y2 α β
