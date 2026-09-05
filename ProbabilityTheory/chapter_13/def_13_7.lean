/-
TASK ID: def_13_7
TYPE: Definition
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_6
import ProbabilityTheory.chapter_12.thm_12_6




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section



structure Def137GuardedCondExpEq {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓖 : MeasurableSpace Ω) (Z W : Ω → ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  sub_ambient : 𝓖 ≤ 𝓕
  integrable : Integrable Z P
  condExp_eq : P[Z | 𝓖] =ᵐ[P] W



def def_13_7_oneStepCondition {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (X : ℕ → Ω → ℝ) : Prop :=
  ∀ n : ℕ,
    Def137GuardedCondExpEq (𝓕 := 𝓕) P (𝓕n n) (X (n + 1)) (X n)



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
  (h.2.2.2 n).condExp_eq

 
theorem def_13_7_isProbabilityMeasure {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (h : def_13_7 P 𝓕n X) : IsProbabilityMeasure P :=
  (h.2.2.2 0).isProbabilityMeasure



theorem def_13_7_condExp_integrable_succ
    {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (h : def_13_7 P 𝓕n X) (n : ℕ) : Integrable (X (n + 1)) P :=
  (h.2.2.2 n).integrable



theorem def_13_7_condExp_sub_ambient
    {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (h : def_13_7 P 𝓕n X) (n : ℕ) : 𝓕n n ≤ 𝓕 :=
  (h.2.2.2 n).sub_ambient



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
  ∀ n : ℕ,
    Def137GuardedCondExpEq (𝓕 := inferInstance) P (def_13_7_historySigma Y n)
      (X (n + 1)) (X n)
