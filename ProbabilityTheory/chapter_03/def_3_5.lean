/-
TASK ID: def_3_5
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.Basic

open Set Filter



structure StieltjesMeasureFunction where
   
  toFun : ℝ → ℝ
   
  non_decreasing : Monotone toFun
   
  right_continuous : ∀ x : ℝ, ContinuousWithinAt toFun (Ici x) x

 
instance : CoeFun StieltjesMeasureFunction (fun _ => ℝ → ℝ) where
  coe F := F.toFun



def StieltjesMeasureFunction.toStieltjesFunction (F : StieltjesMeasureFunction) :
    StieltjesFunction ℝ where
  toFun := F.toFun
  mono' := F.non_decreasing
  right_continuous' := F.right_continuous
