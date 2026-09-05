/-
TASK ID: prob_13_9
TYPE: Problem
SOURCE PLAN: chapter13-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.common_support.chapter13_stopping_support
import ProbabilityTheory.chapter_13.def_13_7




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



theorem prob_13_9_observation_measurable_natural {Ω : Type*}
    (X : ℕ → Ω → ℝ) (n : ℕ) :
    @Measurable Ω ℝ (chapter13_oneIndexedNaturalFiltration X (n + 1)) _
      (X (n + 1)) := by
  let k : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
  have hcoord : Measurable (fun z : Fin (n + 1) → ℝ => z k) :=
    measurable_pi_apply k
  have hhist := chapter13_history_measurable_self X (n + 1)
  have heq :
      (fun z : Fin (n + 1) → ℝ => z k) ∘
          chapter13_oneIndexedHistory X (n + 1) =
        X (n + 1) := by
    funext ω
    rfl
  rw [← heq]
  exact hcoord.comp hhist



theorem prob_13_9_innovation_integrable {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hXint : ∀ n : ℕ, Integrable (X (n + 1)) P) :
    ∀ n : ℕ, Integrable (prob_13_9_innovation P 𝓕n X n) P := by
  intro n
  cases n with
  | zero =>
      change Integrable (0 : Ω → ℝ) P
      exact integrable_zero _ _ _
  | succ n =>
      haveI : SigmaFinite (P.trim (hfiltration.1 n)) := by infer_instance
      exact (hXint n).sub integrable_condExp



theorem prob_13_9_innovation_adapted {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (_hXint : ∀ n : ℕ, Integrable (X (n + 1)) P)
    (hXmeas : ∀ n : ℕ,
      @Measurable Ω ℝ (𝓕n (n + 1)) _ (X (n + 1))) :
    def_13_6_adapted 𝓕n (prob_13_9_innovation P 𝓕n X) := by
  intro n
  cases n with
  | zero =>
      change @Measurable Ω ℝ (𝓕n 0) _ (0 : Ω → ℝ)
      exact measurable_const
  | succ n =>
      have hmono : 𝓕n n ≤ 𝓕n (n + 1) :=
        hfiltration.2 n (n + 1) (Nat.le_succ n)
      have hcond :
          @Measurable Ω ℝ (𝓕n (n + 1)) _
            (P[X (n + 1) | 𝓕n n]) :=
        stronglyMeasurable_condExp.measurable.mono hmono (le_refl _)
      exact (hXmeas n).sub hcond

 
theorem prob_13_9_partialSum_integrable {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {Y : ℕ → Ω → ℝ}
    (hYint : ∀ n : ℕ, Integrable (Y n) P) :
    ∀ n : ℕ, Integrable (prob_13_9_partialSum Y n) P := by
  intro n
  induction n with
  | zero =>
      change Integrable (0 : Ω → ℝ) P
      exact integrable_zero _ _ _
  | succ n ih =>
      rw [prob_13_9_partialSum_step]
      exact ih.add (hYint (n + 1))

 
theorem prob_13_9_partialSum_adapted {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {𝓕n : ℕ → MeasurableSpace Ω}
    {Y : ℕ → Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hYadapted : def_13_6_adapted 𝓕n Y) :
    def_13_6_adapted 𝓕n (prob_13_9_partialSum Y) := by
  intro n
  induction n with
  | zero =>
      change @Measurable Ω ℝ (𝓕n 0) _ (0 : Ω → ℝ)
      exact measurable_const
  | succ n ih =>
      rw [prob_13_9_partialSum_step]
      have hprev :
          @Measurable Ω ℝ (𝓕n (n + 1)) _
            (prob_13_9_partialSum Y n) :=
        ih.mono (hfiltration.2 n (n + 1) (Nat.le_succ n)) (le_refl _)
      exact hprev.add (hYadapted (n + 1))



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
  integrable_S : ∀ n : ℕ, Integrable (S n) P
  integrable_Y : ∀ n : ℕ, Integrable (Y n) P
  adapted_S : def_13_6_adapted 𝓕n S
  initial_zero : S 0 = 0
  partial_sum_step : ∀ n : ℕ, S (n + 1) = S n + Y (n + 1)
  innovation_zero : ∀ n : ℕ, P[Y (n + 1) | 𝓕n n] =ᵐ[P] 0



theorem prob_13_9_partial_sums_martingale {Ω : Type*}
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {Y S : ℕ → Ω → ℝ}
    (D : Prob139InnovationPartialSumData P 𝓕n Y S) :
    def_13_7 P 𝓕n S := by
  refine ⟨D.filtration, D.integrable_S, D.adapted_S, ?_⟩
  intro n
  refine ⟨inferInstance, D.filtration.1 n, D.integrable_S (n + 1), ?_⟩
  haveI : SigmaFinite (P.trim (D.filtration.1 n)) := by infer_instance
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
    [𝓕 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : ℕ → Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hIntegrableXsucc : ∀ n : ℕ, Integrable (X (n + 1)) P)
    (hMeasurableXsucc : ∀ n : ℕ,
      @Measurable Ω ℝ (𝓕n (n + 1)) _ (X (n + 1))) :
    def_13_7 P 𝓕n
      (prob_13_9_partialSum (prob_13_9_innovation P 𝓕n X)) := by
  let Y := prob_13_9_innovation P 𝓕n X
  let S := prob_13_9_partialSum Y
  have hIntegrableY : ∀ n : ℕ, Integrable (Y n) P :=
    prob_13_9_innovation_integrable hfiltration hIntegrableXsucc
  have hAdaptedY : def_13_6_adapted 𝓕n Y :=
    prob_13_9_innovation_adapted hfiltration hIntegrableXsucc
      hMeasurableXsucc
  have hIntegrableS : ∀ n : ℕ, Integrable (S n) P :=
    prob_13_9_partialSum_integrable hIntegrableY
  have hAdaptedS : def_13_6_adapted 𝓕n S :=
    prob_13_9_partialSum_adapted hfiltration hAdaptedY
  refine prob_13_9_partial_sums_martingale
    (P := P) (𝓕n := 𝓕n) (Y := Y) (S := S) ?_
  exact {
    filtration := hfiltration
    integrable_S := hIntegrableS
    integrable_Y := hIntegrableY
    adapted_S := hAdaptedS
    initial_zero := prob_13_9_partialSum_zero Y
    partial_sum_step := prob_13_9_partialSum_step Y
    innovation_zero := fun n => by
      haveI : SigmaFinite (P.trim (hfiltration.1 n)) := by infer_instance
      exact prob_13_9_innovation_condExp_zero hfiltration n
        (hIntegrableXsucc n) }



theorem prob_13_9 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (hX0 : X 0 = 0)
    (hMeasurableXsucc : ∀ n : ℕ,
      @Measurable Ω ℝ 𝓕 _ (X (n + 1)))
    (hIntegrableXsucc : ∀ n : ℕ, Integrable (X (n + 1)) P) :
    def_13_7 P (chapter13_oneIndexedNaturalFiltration X)
      (prob_13_9_partialSum
        (prob_13_9_innovation P
          (chapter13_oneIndexedNaturalFiltration X) X)) := by
  have hMeasurableX : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (X n) := by
    intro n
    cases n with
    | zero =>
        rw [hX0]
        exact measurable_const
    | succ n =>
        exact hMeasurableXsucc n
  have hfiltration :
      def_13_6_isFiltration (𝓕 := 𝓕)
        (chapter13_oneIndexedNaturalFiltration X) :=
    chapter13_oneIndexedNaturalFiltration_isFiltration X hMeasurableX
  have hMeasurableNatural : ∀ n : ℕ,
      @Measurable Ω ℝ
        (chapter13_oneIndexedNaturalFiltration X (n + 1)) _
        (X (n + 1)) :=
    prob_13_9_observation_measurable_natural X
  have hIntegrableY : ∀ n : ℕ,
      Integrable
        (prob_13_9_innovation P
          (chapter13_oneIndexedNaturalFiltration X) X n) P :=
    prob_13_9_innovation_integrable hfiltration hIntegrableXsucc
  have hAdaptedY :
      def_13_6_adapted (chapter13_oneIndexedNaturalFiltration X)
        (prob_13_9_innovation P
          (chapter13_oneIndexedNaturalFiltration X) X) :=
    prob_13_9_innovation_adapted hfiltration hIntegrableXsucc
      hMeasurableNatural
  have hIntegrableS : ∀ n : ℕ,
      Integrable
        (prob_13_9_partialSum
          (prob_13_9_innovation P
            (chapter13_oneIndexedNaturalFiltration X) X) n) P :=
    prob_13_9_partialSum_integrable hIntegrableY
  have hAdaptedS :
      def_13_6_adapted (chapter13_oneIndexedNaturalFiltration X)
        (prob_13_9_partialSum
          (prob_13_9_innovation P
            (chapter13_oneIndexedNaturalFiltration X) X)) :=
    prob_13_9_partialSum_adapted hfiltration hAdaptedY
  let Y := prob_13_9_innovation P
    (chapter13_oneIndexedNaturalFiltration X) X
  let S := prob_13_9_partialSum Y
  refine prob_13_9_partial_sums_martingale
    (P := P) (𝓕n := chapter13_oneIndexedNaturalFiltration X)
    (Y := Y) (S := S) ?_
  exact {
    filtration := hfiltration
    integrable_S := hIntegrableS
    integrable_Y := hIntegrableY
    adapted_S := hAdaptedS
    initial_zero := prob_13_9_partialSum_zero Y
    partial_sum_step := prob_13_9_partialSum_step Y
    innovation_zero := fun n => by
      haveI : SigmaFinite (P.trim (hfiltration.1 n)) := by infer_instance
      exact prob_13_9_innovation_condExp_zero hfiltration n
        (hIntegrableXsucc n) }
