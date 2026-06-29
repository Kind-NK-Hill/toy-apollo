/-
TASK ID: def_12_2
TYPE: Definition
SOURCE PLAN: chapter12-l2-norm-inner-product
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_7_3
import ToyApollo.Output.def_12_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable def l2Inner {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ)
    (hX : L2Function P X) (hY : L2Function P Y) : ℝ :=
  P[fun ω => X ω * Y ω]

theorem l2Inner_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → ℝ} (hX : L2Function P X) (hY : L2Function P Y) :
    Integrable (fun ω => X ω * Y ω) P :=
  L2Function.integrable_mul hX hY

noncomputable def l2Norm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hX : L2Function P X) : ℝ :=
  Real.sqrt (l2Inner P X X hX hX)

theorem l2Norm_eq_sqrt_expectation_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hX : L2Function P X) :
    l2Norm P X hX = Real.sqrt (P[fun ω => X ω ^ 2]) := by
  simp [l2Norm, l2Inner, pow_two]

def L2Orthogonal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ)
    (hX : L2Function P X) (hY : L2Function P Y) : Prop :=
  l2Inner P X Y hX hY = 0

theorem l2Orthogonal_iff_uncorrelated_of_mean_zero {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : L2Function P X) (hY : L2Function P Y)
    (hX0 : P[X] = 0) (hY0 : P[Y] = 0) :
    L2Orthogonal P X Y hX hY ↔ Uncorrelated P X Y := by
  rw [L2Orthogonal, l2Inner, Uncorrelated, hX0, hY0, mul_zero]

def ComplexL2Function {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℂ) : Prop :=
  MemLp X (2 : ENNReal) P

noncomputable def complexL2Inner {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℂ)
    (_hX : ComplexL2Function P X) (_hY : ComplexL2Function P Y) : ℂ :=
  ∫ ω, star (X ω) * Y ω ∂P

noncomputable def def_12_2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ)
    (hX : L2Function P X) (hY : L2Function P Y) : ℝ :=
  l2Inner P X Y hX hY
