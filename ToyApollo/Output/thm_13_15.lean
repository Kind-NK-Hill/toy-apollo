/-
TASK ID: thm_13_15
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_13_8
import ToyApollo.Output.def_13_7

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

def thm_13_15_multiStepCondition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (X : ℕ → Ω → ℝ) : Prop :=
  ∀ n m : ℕ, n ≤ m → P[X m | 𝓕n n] =ᵐ[P] X n

theorem thm_13_15_oneStep_of_multiStep {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hMulti : thm_13_15_multiStepCondition P 𝓕n X) :
    def_13_7_oneStepCondition P 𝓕n X := by
  intro n
  exact hMulti n (n + 1) (Nat.le_succ n)

theorem thm_13_15_condExp_self {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n)))
    (n : ℕ) :
    P[X n | 𝓕n n] =ᵐ[P] X n := by
  have hfiltration := def_13_7_isFiltration hM
  haveI : SigmaFinite (P.trim (hfiltration.1 n)) := hSigmaFinite n
  have hcond :
      P[X n | 𝓕n n] = X n :=
    condExp_of_stronglyMeasurable (hfiltration.1 n)
      ((def_13_7_adapted hM n).stronglyMeasurable)
      (def_13_7_integrable hM n)
  rw [hcond]

theorem thm_13_15_multiStep_of_martingale {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim ((def_13_7_isFiltration hM).1 n))) :
    thm_13_15_multiStepCondition P 𝓕n X := by
  intro n m hnm
  revert n
  induction m with
  | zero =>
      intro n hnm
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      exact thm_13_15_condExp_self hM hSigmaFinite 0
  | succ m ih =>
      intro n hnm
      rcases Nat.lt_or_eq_of_le hnm with hlt | heq
      · have hnle_m : n ≤ m := Nat.le_of_lt_succ hlt
        have hfiltration := def_13_7_isFiltration hM
        have hle_nm : 𝓕n n ≤ 𝓕n m :=
          hfiltration.2 n m hnle_m
        haveI : SigmaFinite (P.trim (hfiltration.1 m)) :=
          hSigmaFinite m
        have htower :
            P[P[X (m + 1) | 𝓕n m] | 𝓕n n] =ᵐ[P]
              P[X (m + 1) | 𝓕n n] :=
          condExp_condExp_of_le hle_nm (hfiltration.1 m)
        have hstep : P[X (m + 1) | 𝓕n m] =ᵐ[P] X m :=
          def_13_7_condExp_succ hM m
        calc
          P[X (m + 1) | 𝓕n n]
              =ᵐ[P] P[P[X (m + 1) | 𝓕n m] | 𝓕n n] := htower.symm
          _ =ᵐ[P] P[X m | 𝓕n n] := condExp_congr_ae hstep
          _ =ᵐ[P] X n := ih n hnle_m
      · subst n
        exact thm_13_15_condExp_self hM hSigmaFinite (m + 1)

theorem thm_13_15 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hIntegrable : ∀ n : ℕ, Integrable (X n) P)
    (hAdapted : def_13_6_adapted 𝓕n X)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n))) :
    def_13_7_oneStepCondition P 𝓕n X ↔
      thm_13_15_multiStepCondition P 𝓕n X := by
  constructor
  · intro hOne
    have hM : def_13_7 P 𝓕n X :=
      ⟨hfiltration, hIntegrable, hAdapted, hOne⟩
    exact thm_13_15_multiStep_of_martingale hM hSigmaFinite
  · intro hMulti
    exact thm_13_15_oneStep_of_multiStep hMulti
