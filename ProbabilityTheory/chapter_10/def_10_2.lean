/-
TASK ID: def_10_2
TYPE: Definition
SOURCE PLAN: chapter10-almost-sure-probability
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_10.def_10_1




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory



def deviationEvent {Ω : Type*} (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) (n : ℕ) (ε : ℝ) :
    Set Ω :=
  {ω : Ω | |Xn n ω - X ω| > ε}



def ConvergesInProbability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  (∀ n : ℕ, Measurable (Xn n)) ∧
    Measurable X ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => μ (deviationEvent Xn X n ε)) atTop (nhds 0)

 
def def_10_2 :=
  @ConvergesInProbability
