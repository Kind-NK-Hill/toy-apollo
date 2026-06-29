/-
TASK ID: def_7_1
TYPE: Definition
SOURCE PLAN: 25_chap7_ae_equality
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

def EqualEverywhere {Ω E : Type*} (f g : Ω → E) : Prop :=
  ∀ ω, f ω = g ω

def EqualAlmostEverywhere {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → E) : Prop :=
  ∃ A : Set Ω, MeasurableSet A ∧ μ A = 0 ∧ EqOn f g Aᶜ

def EquivalentFunctions {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → E) : Prop :=
  EqualAlmostEverywhere μ f g

def def_7_1 {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → E) :
    Prop :=
  EquivalentFunctions μ f g
