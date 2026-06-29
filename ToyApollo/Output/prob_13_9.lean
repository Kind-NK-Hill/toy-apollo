/-
TASK ID: prob_13_9
TYPE: Problem
SOURCE PLAN: chapter13-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_13_7

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

def prob_13_9_innovation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => 0
  | n + 1 => X (n + 1) - P[X (n + 1) | 𝓕n n]

def prob_13_9_partialSum {Ω : Type*} (Y : ℕ → Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => 0
  | n + 1 => prob_13_9_partialSum Y n + Y (n + 1)

theorem prob_13_9_partialSum_zero {Ω : Type*} (Y : ℕ → Ω → ℝ) :
    prob_13_9_partialSum Y 0 = 0 := by
  rfl

theorem prob_13_9_partialSum_step {Ω : Type*} (Y : ℕ → Ω → ℝ)
    (n : ℕ) :
    prob_13_9_partialSum Y (n + 1) =
      prob_13_9_partialSum Y n + Y (n + 1) := by
  rfl

theorem prob_13_9_innovation_condExp_zero {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (n : ℕ) (hX : Integrable (X (n + 1)) P)
    [SigmaFinite (P.trim (hfiltration.1 n))] :
    P[prob_13_9_innovation P 𝓕n X (n + 1) | 𝓕n n] =ᵐ[P] 0 := by
  change
    P[X (n + 1) - P[X (n + 1) | 𝓕n n] | 𝓕n n] =ᵐ[P] 0
  have hcondInt : Integrable (P[X (n + 1) | 𝓕n n]) P :=
    integrable_condExp
  have hsub :
      P[X (n + 1) - P[X (n + 1) | 𝓕n n] | 𝓕n n] =ᵐ[P]
        P[X (n + 1) | 𝓕n n] -
          P[P[X (n + 1) | 𝓕n n] | 𝓕n n] :=
    condExp_sub hX hcondInt (𝓕n n)
  have hself :
      P[P[X (n + 1) | 𝓕n n] | 𝓕n n] =ᵐ[P]
        P[X (n + 1) | 𝓕n n] :=
    condExp_condExp_of_le (μ := P) (f := X (n + 1))
      (m₁ := 𝓕n n) (m₂ := 𝓕n n) (m₀ := 𝓕)
      (le_refl (𝓕n n)) (hfiltration.1 n)
  exact hsub.trans <| by
    filter_upwards [hself] with ω hω
    simp [Pi.sub_apply, hω]

structure Prob139InnovationPartialSumData {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (Y S : ℕ → Ω → ℝ) where
  filtration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n
  sigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim (filtration.1 n))
  integrable_S : ∀ n : ℕ, Integrable (S n) P
  integrable_Y : ∀ n : ℕ, Integrable (Y n) P
  adapted_S : def_13_6_adapted 𝓕n S
  initial_zero : S 0 = 0
  partial_sum_step : ∀ n : ℕ, S (n + 1) = S n + Y (n + 1)
  innovation_zero : ∀ n : ℕ, P[Y (n + 1) | 𝓕n n] =ᵐ[P] 0

theorem prob_13_9_partial_sums_martingale {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {Y S : ℕ → Ω → ℝ}
    (D : Prob139InnovationPartialSumData P 𝓕n Y S) :
    def_13_7 P 𝓕n S := by
  refine ⟨D.filtration, D.integrable_S, D.adapted_S, ?_⟩
  intro n
  haveI : SigmaFinite (P.trim (D.filtration.1 n)) := D.sigmaFinite n
  have hself : P[S n | 𝓕n n] = S n :=
    condExp_of_stronglyMeasurable (D.filtration.1 n)
      ((D.adapted_S n).stronglyMeasurable) (D.integrable_S n)
  rw [D.partial_sum_step n]
  have hadd :
      P[S n + Y (n + 1) | 𝓕n n] =ᵐ[P]
        P[S n | 𝓕n n] + P[Y (n + 1) | 𝓕n n] :=
    condExp_add (D.integrable_S n) (D.integrable_Y (n + 1)) (𝓕n n)
  have hsum :
      P[S n | 𝓕n n] + P[Y (n + 1) | 𝓕n n] =ᵐ[P] S n := by
    rw [hself]
    filter_upwards [D.innovation_zero n] with ω hzero
    simp [Pi.add_apply, hzero]
  exact hadd.trans hsum

theorem prob_13_9_innovation_partialSum_martingale {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n)))
    (hIntegrableXsucc : ∀ n : ℕ, Integrable (X (n + 1)) P)
    (hIntegrableY : ∀ n : ℕ,
      Integrable (prob_13_9_innovation P 𝓕n X n) P)
    (hIntegrableS : ∀ n : ℕ,
      Integrable (prob_13_9_partialSum
        (prob_13_9_innovation P 𝓕n X) n) P)
    (hAdaptedS : def_13_6_adapted 𝓕n
      (prob_13_9_partialSum (prob_13_9_innovation P 𝓕n X))) :
    def_13_7 P 𝓕n
      (prob_13_9_partialSum (prob_13_9_innovation P 𝓕n X)) := by
  let Y := prob_13_9_innovation P 𝓕n X
  let S := prob_13_9_partialSum Y
  refine prob_13_9_partial_sums_martingale
    (P := P) (𝓕n := 𝓕n) (Y := Y) (S := S) ?_
  exact {
    filtration := hfiltration
    sigmaFinite := hSigmaFinite
    integrable_S := hIntegrableS
    integrable_Y := hIntegrableY
    adapted_S := hAdaptedS
    initial_zero := prob_13_9_partialSum_zero Y
    partial_sum_step := prob_13_9_partialSum_step Y
    innovation_zero := fun n => by
      haveI : SigmaFinite (P.trim (hfiltration.1 n)) := hSigmaFinite n
      exact prob_13_9_innovation_condExp_zero hfiltration n
        (hIntegrableXsucc n) }

theorem prob_13_9 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n)))
    (hIntegrableXsucc : ∀ n : ℕ, Integrable (X (n + 1)) P)
    (hIntegrableY : ∀ n : ℕ,
      Integrable (prob_13_9_innovation P 𝓕n X n) P)
    (hIntegrableS : ∀ n : ℕ,
      Integrable (prob_13_9_partialSum
        (prob_13_9_innovation P 𝓕n X) n) P)
    (hAdaptedS : def_13_6_adapted 𝓕n
      (prob_13_9_partialSum (prob_13_9_innovation P 𝓕n X))) :
    def_13_7 P 𝓕n
      (prob_13_9_partialSum (prob_13_9_innovation P 𝓕n X)) :=
  prob_13_9_innovation_partialSum_martingale hfiltration hSigmaFinite
    hIntegrableXsucc hIntegrableY hIntegrableS hAdaptedS
