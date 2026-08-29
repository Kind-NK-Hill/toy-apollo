import Mathlib

/-!
Sanitized historical Interface reconstruction for case study `thm_14_8`.
The private source excerpt and prompt-pack metadata are omitted.
The mathematical conditions are collapsed to a toy predicate so this file
isolates the historical public-premise shape and compiles independently.
-/

abbrev Thm148SliceSetup := Nat

def thm148SliceLindeberg (S : Thm148SliceSetup) : Prop := S = 0

def thm148SliceLyapunov (S : Thm148SliceSetup) : Prop := S = 0 ∧ True

def thm148SliceCondition (S : Thm148SliceSetup) : Prop :=
  thm148SliceLindeberg S ∨ thm148SliceLyapunov S

def thm148SliceConclusion (S : Thm148SliceSetup) : Prop := S = 0

/-- Historical public proof package: callers had to supply the missing proof. -/
structure InitialThm148ProofBeyondBook
    (S : Thm148SliceSetup) : Prop where
  lindeberg_triangular_array_clt :
    thm148SliceLindeberg S → thm148SliceConclusion S
  lyapunov_implies_lindeberg :
    thm148SliceLyapunov S → thm148SliceLindeberg S

/-- The historical theorem shape compiled by delegating its core result to `H`. -/
theorem initialThm148
    (S : Thm148SliceSetup)
    (H : InitialThm148ProofBeyondBook S)
    (h : thm148SliceCondition S) :
    thm148SliceConclusion S := by
  rcases h with hL | hY
  · exact H.lindeberg_triangular_array_clt hL
  · exact H.lindeberg_triangular_array_clt (H.lyapunov_implies_lindeberg hY)
