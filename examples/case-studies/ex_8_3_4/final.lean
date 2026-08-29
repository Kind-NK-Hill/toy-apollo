import Mathlib

/-!
Sanitized public Interface slice for case study `ex_8_3_4`.
The private source excerpt and prompt-pack metadata are omitted.
-/

open Finset BigOperators

abbrev ReviewedPlan834 := Fin 2 → Fin 3 → ℝ

def reviewedFeasible834
    (source : Fin 2 → ℝ) (target : Fin 3 → ℝ)
    (plan : ReviewedPlan834) : Prop :=
  (∀ i j, 0 ≤ plan i j) ∧
    (∀ i, ∑ j, plan i j = source i) ∧
    (∀ j, ∑ i, plan i j = target j)

def reviewedCost834 (cost plan : ReviewedPlan834) : ℝ :=
  ∑ i, ∑ j, cost i j * plan i j

/-- The missing optimization contract: compare with every feasible competitor. -/
def reviewedOptimal834
    (source : Fin 2 → ℝ) (target : Fin 3 → ℝ)
    (cost plan : ReviewedPlan834) : Prop :=
  reviewedFeasible834 source target plan ∧
    ∀ competitor, reviewedFeasible834 source target competitor →
      reviewedCost834 cost plan ≤ reviewedCost834 cost competitor

def reviewedHasOptimizer834
    (source : Fin 2 → ℝ) (target : Fin 3 → ℝ)
    (cost : ReviewedPlan834) : Prop :=
  ∃ plan, reviewedOptimal834 source target cost plan

/-- Finite-carrier Wasserstein value retained as a distinct public concept. -/
noncomputable def reviewedWassersteinValue834
    (source : Fin 2 → ℝ) (target : Fin 3 → ℝ)
    (metricCost : ReviewedPlan834) : ℝ :=
  sInf {value : ℝ | ∃ plan,
    reviewedFeasible834 source target plan ∧
      value = reviewedCost834 metricCost plan}

def reviewedWassersteinContract834
    (source : Fin 2 → ℝ) (target : Fin 3 → ℝ)
    (metricCost : ReviewedPlan834) (p : ℕ) : Prop :=
  1 ≤ p ∧ reviewedHasOptimizer834 source target metricCost
