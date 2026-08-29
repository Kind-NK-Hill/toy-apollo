import Mathlib

/-!
Sanitized public Interface slice for case study `ex_8_3_4`.
The private source excerpt and prompt-pack metadata are omitted.
-/

open Finset BigOperators

abbrev InitialPlan834 := Fin 2 → Fin 3 → ℝ

def initialFeasible834
    (source : Fin 2 → ℝ) (target : Fin 3 → ℝ)
    (plan : InitialPlan834) : Prop :=
  (∀ i j, 0 ≤ plan i j) ∧
    (∀ i, ∑ j, plan i j = source i) ∧
    (∀ j, ∑ i, plan i j = target j)

def initialCost834 (cost plan : InitialPlan834) : ℝ :=
  ∑ i, ∑ j, cost i j * plan i j

/-- Initial export: one fixed plan is feasible and its cost equals itself. -/
def initialExport834
    (source : Fin 2 → ℝ) (target : Fin 3 → ℝ)
    (cost fixed : InitialPlan834) : Prop :=
  initialFeasible834 source target fixed ∧
    initialCost834 cost fixed = initialCost834 cost fixed
