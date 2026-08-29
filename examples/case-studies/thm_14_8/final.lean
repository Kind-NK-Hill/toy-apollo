import Mathlib

/-!
Sanitized current Interface check for case study `thm_14_8`.
The private source excerpt and prompt-pack metadata are omitted.
The mathematical conditions are collapsed to a toy predicate so this file
isolates the premise-free public signature and compiles independently.
-/

abbrev Thm148SliceSetup := Nat

def thm148SliceLindeberg (S : Thm148SliceSetup) : Prop := S = 0

def thm148SliceLyapunov (S : Thm148SliceSetup) : Prop := S = 0 ∧ True

def thm148SliceCondition (S : Thm148SliceSetup) : Prop :=
  thm148SliceLindeberg S ∨ thm148SliceLyapunov S

def thm148SliceConclusion (S : Thm148SliceSetup) : Prop := S = 0

theorem thm148SliceOfLindeberg
    (S : Thm148SliceSetup)
    (hL : thm148SliceLindeberg S) :
    thm148SliceConclusion S :=
  hL

theorem thm148SliceOfLyapunov
    (S : Thm148SliceSetup)
    (hY : thm148SliceLyapunov S) :
    thm148SliceConclusion S :=
  hY.1

/-- The reviewed theorem now closes both branches without a proof-package premise. -/
theorem reviewedThm148
    (S : Thm148SliceSetup)
    (h : thm148SliceCondition S) :
    thm148SliceConclusion S := by
  rcases h with hL | hY
  · exact thm148SliceOfLindeberg S hL
  · exact thm148SliceOfLyapunov S hY
