import Mathlib

/-!
Sanitized public Interface slice for case study `def_5_5`.
The private source excerpt and prompt-pack metadata are omitted.
-/

/-- Initial compiling shortcut: the public definition is only a Mathlib alias. -/
def initialDef55 {Ω : Type _} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {n : ℕ} (A : Fin n → Set Ω) : Prop :=
  ProbabilityTheory.iIndepSet A μ
