import Mathlib

/-!
Sanitized public snapshot for case study `def_8_5`.

The private evidence file is identified in `review-timeline.json`. The source
excerpt and machine-local prompt-pack metadata are intentionally omitted.
-/

open MeasureTheory Set

/-- Final Interface: both inputs carry the source probability-measure domain. -/
noncomputable def reviewedTotalVariationDistance
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : ℝ :=
  sSup {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧ d = |P.real A - Q.real A|}

/-- Final exported definition. -/
noncomputable def reviewedDef85
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : ℝ :=
  reviewedTotalVariationDistance P Q
