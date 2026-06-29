/-
TASK ID: def_12_1
TYPE: Definition
SOURCE PLAN: chapter12-l2-norm-inner-product
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_11_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace

def LpFunction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ENNReal) (X : Ω → ℝ) : Prop :=
  MemLp X p μ

def LpFunctionNat {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℕ) (hp : 0 < p) (X : Ω → ℝ) : Prop :=
  LpFunction μ (p : ENNReal) X

def L2Function {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : Prop :=
  LpFunction μ (2 : ENNReal) X

noncomputable def L2Function.toLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : L2Function μ X) : Ω →₂[μ] ℝ :=
  (show MemLp X (2 : ENNReal) μ from hX).toLp X

theorem L2Function.memLp_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : L2Function μ X) :
    LpFunction μ (1 : ENNReal) X := by
  exact (show MemLp X (2 : ENNReal) μ from hX).mono_exponent (by norm_num)

theorem L2Function.integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : L2Function μ X) :
    Integrable X μ := by
  exact (show MemLp X (2 : ENNReal) μ from hX).integrable (by norm_num)

theorem L2Function.cauchySchwarz_inner_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function μ X) (hY : L2Function μ Y) :
    ‖⟪L2Function.toLp hX, L2Function.toLp hY⟫_ℝ‖ ≤
      ‖L2Function.toLp hX‖ * ‖L2Function.toLp hY‖ := by
  exact thm_11_1 (L2Function.toLp hX) (L2Function.toLp hY)

structure L2Function.CauchySchwarzProductSupport {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function μ X) (hY : L2Function μ Y) : Prop where
  inner_bound :
    ‖⟪L2Function.toLp hX, L2Function.toLp hY⟫_ℝ‖ ≤
      ‖L2Function.toLp hX‖ * ‖L2Function.toLp hY‖
  product_integrable : Integrable (fun ω => X ω * Y ω) μ

theorem L2Function.cauchySchwarz_product_support {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : L2Function μ X) (hY : L2Function μ Y) :
    L2Function.CauchySchwarzProductSupport hX hY := by
  have hX2 : Integrable (fun ω => ‖X ω‖ ^ (2 : ℕ)) μ := by
    exact MemLp.integrable_norm_pow
      (show MemLp X ((2 : ℕ) : ENNReal) μ from by simpa using hX)
      (by norm_num)
  have hY2 : Integrable (fun ω => ‖Y ω‖ ^ (2 : ℕ)) μ := by
    exact MemLp.integrable_norm_pow
      (show MemLp Y ((2 : ℕ) : ENNReal) μ from by simpa using hY)
      (by norm_num)
  have hquad :
      Integrable
        (fun ω => (‖X ω‖ ^ (2 : ℕ) + ‖Y ω‖ ^ (2 : ℕ)) / (2 : ℝ)) μ :=
    (hX2.add hY2).div_const 2
  have hmeas : AEStronglyMeasurable (fun ω => X ω * Y ω) μ :=
    (show MemLp X (2 : ENNReal) μ from hX).aestronglyMeasurable.mul
      (show MemLp Y (2 : ENNReal) μ from hY).aestronglyMeasurable
  have hintegrable : Integrable (fun ω => X ω * Y ω) μ := by
    refine Integrable.mono' hquad hmeas ?_
    filter_upwards with ω
    have hineq :
        ‖X ω‖ * ‖Y ω‖ ≤
          (‖X ω‖ ^ (2 : ℕ) + ‖Y ω‖ ^ (2 : ℕ)) / (2 : ℝ) := by
      nlinarith [sq_nonneg (‖X ω‖ - ‖Y ω‖)]
    simpa [norm_mul] using hineq
  exact
    { inner_bound := L2Function.cauchySchwarz_inner_bound hX hY
      product_integrable := hintegrable }

theorem L2Function.integrable_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : L2Function μ X) (hY : L2Function μ Y) :
    Integrable (fun ω => X ω * Y ω) μ :=
  (L2Function.cauchySchwarz_product_support hX hY).product_integrable

def def_12_1 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℕ) (hp : 0 < p) (X : Ω → ℝ) : Prop :=
  LpFunctionNat μ p hp X
