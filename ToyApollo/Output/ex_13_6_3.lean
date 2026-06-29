/-
TASK ID: ex_13_6_3
TYPE: Example_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_13_7
import ToyApollo.Output.ex_13_6_1

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

abbrev ex_13_6_3_naturalFiltration {Ω : Type*}
    (Y : ℕ → Ω → ℝ) : ℕ → MeasurableSpace Ω :=
  ex_13_6_1_naturalFiltration Y

def ex_13_6_3_process {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (X : Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n => P[X | 𝓕n n]

theorem ex_13_6_3_process_adapted {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω) (X : Ω → ℝ) :
    def_13_6_adapted 𝓕n (ex_13_6_3_process P 𝓕n X) := by
  intro n
  exact stronglyMeasurable_condExp.measurable

theorem ex_13_6_3_process_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω) (X : Ω → ℝ) :
    ∀ n : ℕ, Integrable (ex_13_6_3_process P 𝓕n X n) P := by
  intro n
  exact integrable_condExp

theorem ex_13_6_3_oneStepCondition {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n))) :
    def_13_7_oneStepCondition P 𝓕n
      (ex_13_6_3_process P 𝓕n X) := by
  intro n
  have hle : 𝓕n n ≤ 𝓕n (n + 1) :=
    hfiltration.2 n (n + 1) (Nat.le_succ n)
  haveI : SigmaFinite (P.trim (hfiltration.1 (n + 1))) :=
    hSigmaFinite (n + 1)
  exact condExp_condExp_of_le hle (hfiltration.1 (n + 1))

theorem ex_13_6_3_doob_martingale {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hSigmaFinite : ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n)))
    (_hXint : Integrable X P) :
    def_13_7 P 𝓕n (ex_13_6_3_process P 𝓕n X) := by
  exact ⟨hfiltration, ex_13_6_3_process_integrable P 𝓕n X,
    ex_13_6_3_process_adapted P 𝓕n X,
    ex_13_6_3_oneStepCondition hfiltration hSigmaFinite⟩

theorem ex_13_6_3 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hY : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (Y n))
    (hXint : Integrable X P) :
    def_13_7 P (ex_13_6_3_naturalFiltration Y)
      (ex_13_6_3_process P (ex_13_6_3_naturalFiltration Y) X) := by
  have hfiltration :
      def_13_6_isFiltration (𝓕 := 𝓕) (ex_13_6_3_naturalFiltration Y) :=
    ex_13_6_1_naturalFiltration_isFiltration Y hY
  have hSigmaFinite :
      ∀ n : ℕ, SigmaFinite (P.trim (hfiltration.1 n)) := by
    intro n
    infer_instance
  exact ex_13_6_3_doob_martingale hfiltration hSigmaFinite hXint
