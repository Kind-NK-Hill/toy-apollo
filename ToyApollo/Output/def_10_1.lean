/-
TASK ID: def_10_1
TYPE: Definition
SOURCE PLAN: chapter10-almost-sure-probability
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory

def ConvergesSurely {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  (∀ n : ℕ, AEStronglyMeasurable (Xn n) μ) ∧
    AEStronglyMeasurable X μ ∧
      ∀ ω : Ω, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

def ConvergesAlmostSurely {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  (∀ n : ℕ, AEStronglyMeasurable (Xn n) μ) ∧
    AEStronglyMeasurable X μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

def ConvergesAlmostSurelyOnEvent {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  (∀ n : ℕ, AEStronglyMeasurable (Xn n) μ) ∧
    AEStronglyMeasurable X μ ∧
      ∃ E : Set Ω, MeasurableSet E ∧ μ Eᶜ = 0 ∧
        ∀ ω ∈ E, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

theorem convergesAlmostSurelyOnEvent_iff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    ConvergesAlmostSurelyOnEvent μ Xn X ↔ ConvergesAlmostSurely μ Xn X := by
  constructor
  · rintro ⟨hXn, hX, E, hE, hE_full, hconv⟩
    refine ⟨hXn, hX, ae_iff.2 ?_⟩
    refine MeasureTheory.measure_mono_null ?_ hE_full
    intro ω hbad
    change ω ∉ E
    intro hω
    exact hbad (hconv ω hω)
  · rintro ⟨hXn, hX, hconv⟩
    have hbad :
        μ {ω : Ω | ¬ Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))} = 0 :=
      ae_iff.1 hconv
    obtain ⟨N, hbadN, hN_meas, hN_null⟩ :=
      exists_measurable_superset_of_null hbad
    refine ⟨hXn, hX, Nᶜ, hN_meas.compl, ?_, ?_⟩
    · simpa only [compl_compl] using hN_null
    · intro ω hω
      by_contra hω_bad
      exact hω (hbadN hω_bad)

theorem convergesAlmostSurely_iff_exists_measure_one_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    ConvergesAlmostSurely μ Xn X ↔
      (∀ n : ℕ, AEStronglyMeasurable (Xn n) μ) ∧
        AEStronglyMeasurable X μ ∧
          ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
            ∀ ω ∈ E, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω)) := by
  constructor
  · intro hconv
    rcases (convergesAlmostSurelyOnEvent_iff μ Xn X).2 hconv with
      ⟨hXn, hX, E, hE, hE_full, hE_conv⟩
    refine ⟨hXn, hX, E, hE, ?_, hE_conv⟩
    have hfin : μ Eᶜ ≠ ⊤ := by
      rw [hE_full]
      simp
    simpa [hE_full, MeasureTheory.IsProbabilityMeasure.measure_univ] using
      (MeasureTheory.measure_compl hE.compl hfin)
  · rintro ⟨hXn, hX, E, hE, hE_one, hE_conv⟩
    apply (convergesAlmostSurelyOnEvent_iff μ Xn X).1
    refine ⟨hXn, hX, E, hE, ?_, hE_conv⟩
    have hfin : μ E ≠ ⊤ := by
      rw [hE_one]
      simp
    rw [MeasureTheory.measure_compl hE hfin]
    simp [hE_one, MeasureTheory.IsProbabilityMeasure.measure_univ]

def def_10_1 :=
  (@ConvergesSurely, @ConvergesAlmostSurely, @ConvergesAlmostSurelyOnEvent)
