import Mathlib

/-
TASK ID: prob_5_2
TYPE: Problem
SOURCE PLAN: 18_chap5_problems
TASK CONTENT:
\item Prove that in any probability space $(\Omega, \mathcal{F}, P)$, the empty set is independent of any event in the $\sigma$-algebra $\mathcal{F}$.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

theorem prob_5_2 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A) :
    IndepSet (∅ : Set Ω) A P :=
  indepSet_empty_left A
