import Mathlib

/-!
Sanitized public snapshot for case study `def_10_1`.

The private evidence file is identified in `review-timeline.json`. The source
excerpt and machine-local prompt-pack metadata are intentionally omitted.
-/

open Filter MeasureTheory

/-- Initial sure-convergence Interface: pointwise convergence only. -/
def InitialConvergesSurely {Ω : Type*}
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∀ ω : Ω, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

/-- Initial almost-everywhere Interface. -/
def InitialConvergesAlmostSurely
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))

/-- Initial event Interface: `μ E = 1` is incorrectly used for any measure. -/
def InitialConvergesAlmostSurelyOnEvent
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∃ E : Set Ω, MeasurableSet E ∧ μ E = 1 ∧
    ∀ ω ∈ E, Tendsto (fun n : ℕ => Xn n ω) atTop (nhds (X ω))
