/-
TASK ID: def_13_9
TYPE: Definition
SOURCE PLAN: chapter13-martingale-stopping-time
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_8




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section



def def_13_9_stoppedIndex {Ω : Type*}
    (T : Ω → WithTop ℕ) (n : ℕ) (ω : Ω) : ℕ :=
  match T ω with
  | none => n
  | some k => min k n



def def_13_9_stoppedProcess {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) : ℕ → Ω → S :=
  fun n ω => X (def_13_9_stoppedIndex T n ω) ω



def def_13_9 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (P : Measure Ω) (𝓕n : ℕ → MeasurableSpace Ω)
    (X : ℕ → Ω → ℝ) (T : Ω → WithTop ℕ)
    (Y : ℕ → Ω → ℝ) : Prop :=
  def_13_7 P 𝓕n X ∧
    def_13_8 𝓕n T ∧
      Y = def_13_9_stoppedProcess X T

 
theorem def_13_9_martingale {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω}
    {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ}
    {Y : ℕ → Ω → ℝ} (h : def_13_9 P 𝓕n X T Y) :
    def_13_7 P 𝓕n X :=
  h.1



theorem def_13_9_stoppingTime {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω}
    {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ}
    {Y : ℕ → Ω → ℝ} (h : def_13_9 P 𝓕n X T Y) :
    def_13_8 𝓕n T :=
  h.2.1

 
theorem def_13_9_process {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕n : ℕ → MeasurableSpace Ω}
    {X : ℕ → Ω → ℝ} {T : Ω → WithTop ℕ}
    {Y : ℕ → Ω → ℝ} (h : def_13_9 P 𝓕n X T Y) :
    Y = def_13_9_stoppedProcess X T :=
  h.2.2

theorem def_13_9_apply {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (n : ℕ) (ω : Ω) :
    def_13_9_stoppedProcess X T n ω =
      X (def_13_9_stoppedIndex T n ω) ω :=
  rfl

theorem def_13_9_stoppedIndex_top {Ω : Type*}
    (T : Ω → WithTop ℕ) (n : ℕ) (ω : Ω) (hT : T ω = ⊤) :
    def_13_9_stoppedIndex T n ω = n := by
  simp [def_13_9_stoppedIndex, hT]

theorem def_13_9_stoppedIndex_after_stop {Ω : Type*}
    (T : Ω → WithTop ℕ) (n k : ℕ) (ω : Ω)
    (hT : T ω = (k : WithTop ℕ)) (hkn : k ≤ n) :
    def_13_9_stoppedIndex T n ω = k := by
  simp [def_13_9_stoppedIndex, hT, Nat.min_eq_left hkn]

theorem def_13_9_stoppedProcess_after_stop {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (n k : ℕ) (ω : Ω)
    (hT : T ω = (k : WithTop ℕ)) (hkn : k ≤ n) :
    def_13_9_stoppedProcess X T n ω = X k ω := by
  simp [def_13_9_stoppedProcess,
    def_13_9_stoppedIndex_after_stop T n k ω hT hkn]

theorem def_13_9_stoppedProcess_top {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (n : ℕ) (ω : Ω)
    (hT : T ω = ⊤) :
    def_13_9_stoppedProcess X T n ω = X n ω := by
  simp [def_13_9_stoppedProcess,
    def_13_9_stoppedIndex_top T n ω hT]

theorem def_13_9_matches_stoppedValue_after_stop {Ω S : Type*}
    (X : ℕ → Ω → S) (T : Ω → WithTop ℕ) (n k : ℕ) (ω : Ω)
    (hT : T ω = (k : WithTop ℕ)) (hkn : k ≤ n) :
    some (def_13_9_stoppedProcess X T n ω) =
      def_13_8_stoppedValue X T ω := by
  simp [def_13_9_stoppedProcess,
    def_13_9_stoppedIndex_after_stop T n k ω hT hkn,
    def_13_8_stoppedValue, hT]
