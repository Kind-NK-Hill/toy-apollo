/-
TASK ID: def_13_5
TYPE: Definition
SOURCE PLAN: chapter13-sub-sigma-algebra
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.def_13_3
import ProbabilityTheory.chapter_13.def_13_4




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

noncomputable section

 
def def_13_5_eventIndicator {Ω : Type*} (A : Set Ω) : Ω → ℝ :=
  A.indicator (fun _ => (1 : ℝ))



def def_13_5 {Ω S : Type*} [𝓕 : MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (A : Set Ω) (_hA : IsMeasurableIn 𝓕 A)
    (X : Ω → S) (hσX : IsSubSigmaField (def_13_4_sigma X) 𝓕)
    (CP : Ω → ℝ) : Prop :=
  @def_13_4 Ω S 𝓕 _ P X hσX (def_13_5_eventIndicator A) CP



def def_13_5_versionAsFunctionOfObservation {Ω S : Type*}
    (Y : Ω → S) (g : S → ℝ) (CE : Ω → ℝ) : Prop :=
  CE = g ∘ Y



theorem def_13_5_apply_versionAsFunctionOfObservation {Ω S : Type*}
    (Y : Ω → S) (g : S → ℝ) :
    def_13_5_versionAsFunctionOfObservation Y g (g ∘ Y) := by
  rfl
