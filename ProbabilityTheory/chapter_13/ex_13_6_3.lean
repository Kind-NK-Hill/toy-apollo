/-
TASK ID: ex_13_6_3
TYPE: Example_Proof
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_7
import ProbabilityTheory.chapter_13.ex_13_6_1




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

 
abbrev ex_13_6_3_naturalFiltration {Ω : Type*}
    (Y : ℕ → Ω → ℝ) : ℕ → MeasurableSpace Ω :=
  ex_13_6_1_naturalFiltration Y



def ex_13_6_3_process {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (X : Ω → ℝ) (hXint : Integrable X P) : ℕ → Ω → ℝ :=
  let Xint : {f : Ω → ℝ // Integrable f P} := ⟨X, hXint⟩
  fun n => P[Xint.1 | 𝓕n n]



theorem ex_13_6_3_process_adapted {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω} {X : Ω → ℝ}
    (hXint : Integrable X P) :
    def_13_6_adapted 𝓕n (ex_13_6_3_process P 𝓕n X hXint) := by
  intro n
  exact stronglyMeasurable_condExp.measurable



theorem ex_13_6_3_process_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : Ω → ℝ}
    (hfiltration : def_13_6_isFiltration 𝓕n)
    (hXint : Integrable X P) :
    ∀ n : ℕ, Integrable (ex_13_6_3_process P 𝓕n X hXint n) P := by
  intro n
  letI : SigmaFinite (P.trim (hfiltration.1 n)) := by infer_instance
  change Integrable (P[X | 𝓕n n]) P
  have hbranch :
      P[X | 𝓕n n] =ᵐ[P]
        (condExpL1CLM ℝ (hfiltration.1 n) P (hXint.toL1 X) : Ω → ℝ) := by
    refine (condExp_ae_eq_condExpL1 (hfiltration.1 n) X).trans ?_
    rw [condExpL1_eq hXint]
  exact (L1.integrable_coeFn
    (condExpL1CLM ℝ (hfiltration.1 n) P (hXint.toL1 X))).congr hbranch.symm

 
theorem ex_13_6_3_oneStepCondition {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hXint : Integrable X P) :
    def_13_7_oneStepCondition P 𝓕n
      (ex_13_6_3_process P 𝓕n X hXint) := by
  intro n
  refine ⟨inferInstance, hfiltration.1 n,
    ex_13_6_3_process_integrable hfiltration hXint (n + 1), ?_⟩
  have hle : 𝓕n n ≤ 𝓕n (n + 1) :=
    hfiltration.2 n (n + 1) (Nat.le_succ n)
  letI : SigmaFinite (P.trim (hfiltration.1 n)) := by infer_instance
  letI : SigmaFinite (P.trim (hfiltration.1 (n + 1))) := by infer_instance
  exact condExp_condExp_of_le hle (hfiltration.1 (n + 1))

 
theorem ex_13_6_3_doob_martingale {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕n : ℕ → MeasurableSpace Ω} {X : Ω → ℝ}
    (hfiltration : def_13_6_isFiltration (𝓕 := 𝓕) 𝓕n)
    (hXint : Integrable X P) :
    def_13_7 P 𝓕n (ex_13_6_3_process P 𝓕n X hXint) := by
  exact ⟨hfiltration, ex_13_6_3_process_integrable hfiltration hXint,
    ex_13_6_3_process_adapted hXint,
    ex_13_6_3_oneStepCondition hfiltration hXint⟩



theorem ex_13_6_3 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hY : ∀ n : ℕ, @Measurable Ω ℝ 𝓕 _ (Y (n + 1)))
    (hXint : Integrable X P) :
    def_13_7 P (ex_13_6_3_naturalFiltration Y)
      (ex_13_6_3_process P (ex_13_6_3_naturalFiltration Y) X hXint) := by
  have hfiltration :
      def_13_6_isFiltration (𝓕 := 𝓕) (ex_13_6_3_naturalFiltration Y) :=
    ex_13_6_1_naturalFiltration_isFiltration Y hY
  exact ex_13_6_3_doob_martingale hfiltration hXint
