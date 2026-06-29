/-
TASK ID: def_13_8
TYPE: Definition
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_13_7

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section

def def_13_8_isStoppingTime {Ω : Type*}
    (𝓕n : ℕ → MeasurableSpace Ω) (T : Ω → WithTop ℕ) : Prop :=
  ∀ n : ℕ, @MeasurableSet Ω (𝓕n n) {ω | T ω ≤ (n : WithTop ℕ)}

def def_13_8 {Ω : Type*}
    (𝓕n : ℕ → MeasurableSpace Ω) (T : Ω → WithTop ℕ) : Prop :=
  def_13_8_isStoppingTime 𝓕n T

theorem def_13_8_event_le_measurable {Ω : Type*}
    {𝓕n : ℕ → MeasurableSpace Ω} {T : Ω → WithTop ℕ}
    (hT : def_13_8 𝓕n T) (n : ℕ) :
    @MeasurableSet Ω (𝓕n n) {ω | T ω ≤ (n : WithTop ℕ)} :=
  hT n

def def_13_8_history {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) :
    Ω → Fin (n + 1) → ℝ :=
  fun ω k => X k.1 ω

@[reducible]
def def_13_8_historySigma {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) :
    MeasurableSpace Ω :=
  (inferInstance : MeasurableSpace (Fin (n + 1) → ℝ)).comap
    (def_13_8_history X n)

@[reducible]
def def_13_8_naturalFiltration {Ω : Type*}
    (X : ℕ → Ω → ℝ) : ℕ → MeasurableSpace Ω :=
  fun n => def_13_8_historySigma X n

def def_13_8_stoppingTimeForSequence {Ω : Type*}
    (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ) : Prop :=
  def_13_8 (def_13_8_naturalFiltration X) T

theorem def_13_8_sequence_event_le_measurable {Ω : Type*}
    {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ}
    (hT : def_13_8_stoppingTimeForSequence X T) (n : ℕ) :
    @MeasurableSet Ω (def_13_8_historySigma X n)
      {ω | T ω ≤ (n : WithTop ℕ)} :=
  hT n

def def_13_8_stoppedValue {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) : Ω → Option S :=
  fun ω =>
    match T ω with
    | none => none
    | some n => some (X n ω)

theorem def_13_8_stoppedValue_finite {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (ω : Ω) (n : ℕ)
    (hT : T ω = (n : WithTop ℕ)) :
    def_13_8_stoppedValue X T ω = some (X n ω) := by
  simp [def_13_8_stoppedValue, hT]

theorem def_13_8_stoppedValue_top {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (ω : Ω)
    (hT : T ω = ⊤) :
    def_13_8_stoppedValue X T ω = none := by
  simp [def_13_8_stoppedValue, hT]
