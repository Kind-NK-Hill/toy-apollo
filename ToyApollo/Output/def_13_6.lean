/-
TASK ID: def_13_6
TYPE: Definition
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section

def def_13_6_isFiltration {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (𝓕n : ℕ → MeasurableSpace Ω) : Prop :=
  (∀ n : ℕ, 𝓕n n ≤ 𝓕) ∧
    ∀ n m : ℕ, n ≤ m → 𝓕n n ≤ 𝓕n m

def def_13_6_adapted {Ω S : Type*} [MeasurableSpace S]
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → S) : Prop :=
  ∀ n : ℕ, @Measurable Ω S (𝓕n n) _ (X n)

@[reducible]
def def_13_6_trivialSigmaField (Ω : Type*) : MeasurableSpace Ω :=
  ⊥

def def_13_6_startsTrivial {Ω : Type*}
    (𝓕n : ℕ → MeasurableSpace Ω) : Prop :=
  𝓕n 0 = def_13_6_trivialSigmaField Ω

theorem def_13_6_mono {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {𝓕n : ℕ → MeasurableSpace Ω} (h : def_13_6_isFiltration 𝓕n)
    {n m : ℕ} (hnm : n ≤ m) :
    𝓕n n ≤ 𝓕n m :=
  h.2 n m hnm

theorem def_13_6_sub_ambient {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {𝓕n : ℕ → MeasurableSpace Ω} (h : def_13_6_isFiltration 𝓕n)
    (n : ℕ) :
    𝓕n n ≤ 𝓕 :=
  h.1 n

def def_13_6 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (𝓕n : ℕ → MeasurableSpace Ω) : Prop :=
  def_13_6_isFiltration 𝓕n
