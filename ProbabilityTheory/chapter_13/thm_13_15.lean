/-
TASK ID: thm_13_15
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.thm_13_8
import ProbabilityTheory.chapter_13.def_13_7




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section



def thm_13_15_multiStepCondition {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (X : ℕ → Ω → ℝ) : Prop :=
  ∀ n m : ℕ, n ≤ m →
    Def137GuardedCondExpEq (𝓕 := 𝓕) P (𝓕n n) (X m) (X n)



theorem thm_13_15_oneStep_of_multiStep {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hMulti : thm_13_15_multiStepCondition P 𝓕n X) :
    def_13_7_oneStepCondition P 𝓕n X := by
  intro n
  exact hMulti n (n + 1) (Nat.le_succ n)



theorem thm_13_15_condExp_self {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X)
    (n : ℕ) :
    P[X n | 𝓕n n] =ᵐ[P] X n := by
  letI : IsProbabilityMeasure P := def_13_7_isProbabilityMeasure hM
  have hfiltration := def_13_7_isFiltration hM
  haveI : SigmaFinite (P.trim (hfiltration.1 n)) := inferInstance
  have hcond :
      P[X n | 𝓕n n] = X n :=
    condExp_of_stronglyMeasurable (hfiltration.1 n)
      ((def_13_7_adapted hM n).stronglyMeasurable)
      (def_13_7_integrable hM n)
  rw [hcond]



theorem thm_13_15_multiStep_of_martingale {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X) :
    thm_13_15_multiStepCondition P 𝓕n X := by
  letI : IsProbabilityMeasure P := def_13_7_isProbabilityMeasure hM
  intro n m hnm
  refine ⟨def_13_7_isProbabilityMeasure hM,
    (def_13_7_isFiltration hM).1 n, def_13_7_integrable hM m, ?_⟩
  revert n
  induction m with
  | zero =>
      intro n hnm
      have hn : n = 0 := Nat.eq_zero_of_le_zero hnm
      subst n
      exact thm_13_15_condExp_self hM 0
  | succ m ih =>
      intro n hnm
      rcases Nat.lt_or_eq_of_le hnm with hlt | heq
      · have hnle_m : n ≤ m := Nat.le_of_lt_succ hlt
        have hfiltration := def_13_7_isFiltration hM
        have hle_nm : 𝓕n n ≤ 𝓕n m :=
          hfiltration.2 n m hnle_m
        haveI : SigmaFinite (P.trim (hfiltration.1 m)) :=
          inferInstance
        have htower :
            P[P[X (m + 1) | 𝓕n m] | 𝓕n n] =ᵐ[P]
              P[X (m + 1) | 𝓕n n] :=
          (thm_13_8 (P := P) (𝓖 := 𝓕n m) (𝓗 := 𝓕n n)
            (hfiltration.1 m) hle_nm
            (def_13_7_integrable hM (m + 1))).symm
        have hstep : P[X (m + 1) | 𝓕n m] =ᵐ[P] X m :=
          def_13_7_condExp_succ hM m
        calc
          P[X (m + 1) | 𝓕n n]
              =ᵐ[P] P[P[X (m + 1) | 𝓕n m] | 𝓕n n] := htower.symm
          _ =ᵐ[P] P[X m | 𝓕n n] := condExp_congr_ae hstep
          _ =ᵐ[P] X n := ih n hnle_m
      · subst n
        exact thm_13_15_condExp_self hM (m + 1)



theorem thm_13_15 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hIntegrable : ∀ n : ℕ, Integrable (X n) P)
    (hAdapted : def_13_6_adapted 𝓕n X) :
    def_13_7_oneStepCondition P 𝓕n X ↔
      thm_13_15_multiStepCondition P 𝓕n X := by
  constructor
  · intro hOne
    have hM : def_13_7 P 𝓕n X :=
      ⟨hfiltration, hIntegrable, hAdapted, hOne⟩
    exact thm_13_15_multiStep_of_martingale hM
  · intro hMulti
    exact thm_13_15_oneStep_of_multiStep hMulti



theorem thm_13_15_expectation_constant {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hM : def_13_7 P 𝓕n X) (n : ℕ) :
    ∫ ω, X n ω ∂P = ∫ ω, X 0 ω ∂P := by
  have hfiltration := def_13_7_isFiltration hM
  haveI : SigmaFinite (P.trim (hfiltration.1 0)) := inferInstance
  calc
    ∫ ω, X n ω ∂P = ∫ ω, P[X n | 𝓕n 0] ω ∂P :=
      (integral_condExp (hfiltration.1 0)).symm
    _ = ∫ ω, X 0 ω ∂P :=
      integral_congr_ae
        (thm_13_15_multiStep_of_martingale hM
          0 n (Nat.zero_le n)).condExp_eq
