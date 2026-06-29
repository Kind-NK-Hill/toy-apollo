/-
TASK ID: ex_6_1_1
TYPE: Example_Proof
SOURCE PLAN: 19_chap6_simple_functions
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Function.SimpleFunc

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem ex_6_1_1 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (X : SimpleFunc Ω ENNReal) :
    X.lintegral μ = Finset.sum X.range (fun x => x * μ (X ⁻¹' {x})) := by
  simpa using
    (MeasureTheory.SimpleFunc.map_lintegral (μ := μ) (g := fun x : ENNReal => x) X)
