/-
TASK ID: def_10_1
TYPE: Definition
SOURCE PLAN: chapter10-almost-sure-probability
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

def ConvergesSurely {Ω : Type*} (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∀ ω : Ω, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

def ConvergesAlmostSurely {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

def ConvergesAlmostSurelyOnEvent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
    ∀ ω ∈ E, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

def def_10_1 :=
  (@ConvergesSurely, @ConvergesAlmostSurely, @ConvergesAlmostSurelyOnEvent)
