import Mathlib

/-!
Sanitized public snapshot for case study `def_10_1`.

The private evidence file is identified in `review-timeline.json`. The source
excerpt and machine-local prompt-pack metadata are intentionally omitted.
-/

open Filter MeasureTheory

/-- Reviewed sure convergence with the random-variable carrier in its Interface. -/
def ReviewedConvergesSurely
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  (∀ n : ℕ, AEStronglyMeasurable (Xn n) μ) ∧
    AEStronglyMeasurable X μ ∧
      ∀ ω : Ω, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

/-- Reviewed almost-sure convergence in Mathlib's almost-everywhere form. -/
def ReviewedConvergesAlmostSurely
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  (∀ n : ℕ, AEStronglyMeasurable (Xn n) μ) ∧
    AEStronglyMeasurable X μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

/-- Reviewed full-event form for an arbitrary measure. -/
def ReviewedConvergesAlmostSurelyOnEvent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  (∀ n : ℕ, AEStronglyMeasurable (Xn n) μ) ∧
    AEStronglyMeasurable X μ ∧
      ∃ E : Set Ω, MeasurableSet E ∧ μ Eᶜ = 0 ∧
        ∀ ω ∈ E, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

/-- The measurable full-event Interface is equivalent to the a.e. Interface. -/
theorem reviewedConvergesAlmostSurelyOnEventIff
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    ReviewedConvergesAlmostSurelyOnEvent μ Xn X ↔
      ReviewedConvergesAlmostSurely μ Xn X := by
  constructor
  · rintro ⟨hXn, hX, E, hE, hEFull, hConverges⟩
    refine ⟨hXn, hX, ae_iff.2 ?_⟩
    refine MeasureTheory.measure_mono_null ?_ hEFull
    intro ω hBad
    change ω ∉ E
    intro hω
    exact hBad (hConverges ω hω)
  · rintro ⟨hXn, hX, hConverges⟩
    have hBad :
        μ {ω : Ω | ¬ Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))} = 0 :=
      ae_iff.1 hConverges
    obtain ⟨N, hBadN, hNMeasurable, hNNull⟩ :=
      exists_measurable_superset_of_null hBad
    refine ⟨hXn, hX, Nᶜ, hNMeasurable.compl, ?_, ?_⟩
    · simpa only [compl_compl] using hNNull
    · intro ω hω
      by_contra hωBad
      exact hω (hBadN hωBad)

/-- On a probability space, full event means probability-one event. -/
theorem reviewedConvergesAlmostSurelyIffExistsMeasureOneEvent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) :
    ReviewedConvergesAlmostSurely μ Xn X ↔
      (∀ n : ℕ, AEStronglyMeasurable (Xn n) μ) ∧
        AEStronglyMeasurable X μ ∧
          ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
            ∀ ω ∈ E, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω)) := by
  constructor
  · intro hConverges
    rcases (reviewedConvergesAlmostSurelyOnEventIff μ Xn X).2 hConverges with
      ⟨hXn, hX, E, hE, hEFull, hEConverges⟩
    refine ⟨hXn, hX, E, hE, ?_, hEConverges⟩
    have hFinite : μ Eᶜ ≠ ⊤ := by
      rw [hEFull]
      simp
    simpa [hEFull, MeasureTheory.IsProbabilityMeasure.measure_univ] using
      (MeasureTheory.measure_compl hE.compl hFinite)
  · rintro ⟨hXn, hX, E, hE, hEOne, hEConverges⟩
    apply (reviewedConvergesAlmostSurelyOnEventIff μ Xn X).1
    refine ⟨hXn, hX, E, hE, ?_, hEConverges⟩
    have hFinite : μ E ≠ ⊤ := by
      rw [hEOne]
      simp
    rw [MeasureTheory.measure_compl hE hFinite]
    simp [hEOne, MeasureTheory.IsProbabilityMeasure.measure_univ]
