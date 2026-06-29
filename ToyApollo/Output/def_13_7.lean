/-
TASK ID: def_13_7
TYPE: Definition
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_13_6
import ToyApollo.Output.thm_12_6

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

def def_13_7_oneStepCondition {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (X : ℕ → Ω → ℝ) : Prop :=
  ∀ n : ℕ, P[X (n + 1) | 𝓕n n] =ᵐ[P] X n

def def_13_7 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (X : ℕ → Ω → ℝ) : Prop :=
  def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n ∧
    (∀ n : ℕ, Integrable (X n) P) ∧
    def_13_6_adapted 𝓕n X ∧
    def_13_7_oneStepCondition P 𝓕n X

theorem def_13_7_isFiltration {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (h : def_13_7 P 𝓕n X) :
    def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n :=
  h.1

theorem def_13_7_integrable {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (h : def_13_7 P 𝓕n X) (n : ℕ) :
    Integrable (X n) P :=
  h.2.1 n

theorem def_13_7_adapted {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (h : def_13_7 P 𝓕n X) :
    def_13_6_adapted 𝓕n X :=
  h.2.2.1

theorem def_13_7_condExp_succ {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (h : def_13_7 P 𝓕n X) (n : ℕ) :
    P[X (n + 1) | 𝓕n n] =ᵐ[P] X n :=
  h.2.2.2 n

def def_13_7_history {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) :
    Ω → Fin (n + 1) → ℝ :=
  fun ω k => Y k.1 ω

@[reducible]
def def_13_7_historySigma {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) :
    MeasurableSpace Ω :=
  (inferInstance : MeasurableSpace (Fin (n + 1) → ℝ)).comap
    (def_13_7_history Y n)

theorem def_13_7_history_factorization {Ω : Type*}
    (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : Measurable[def_13_7_historySigma Y n] (X n)) :
    ∃ g : (Fin (n + 1) → ℝ) → ℝ,
      Measurable g ∧ X n = g ∘ def_13_7_history Y n :=
  thm_12_6_factorization (def_13_7_history Y n) (X n) hX

def def_13_7_historyCondition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → ℝ) : Prop :=
  ∀ n : ℕ, P[X (n + 1) | def_13_7_historySigma Y n] =ᵐ[P] X n
