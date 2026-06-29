/-
TASK ID: ex_8_3_2
TYPE: Example_Proof
SOURCE PLAN: 33_chap8_monge_kantorovich
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.ex_3_3_4

-- WRITE FINAL LEAN CODE BELOW

open scoped BigOperators

def finiteMongeCost {n : ℕ} (x y : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, (x i - y (π i)) ^ 2

theorem ex_8_3_2 {n : ℕ} [NeZero n] (x y : Fin n → ℝ) :
    ∃ π : Equiv.Perm (Fin n), ∀ σ : Equiv.Perm (Fin n),
      finiteMongeCost x y π ≤ finiteMongeCost x y σ := by
  classical
  let cost : Equiv.Perm (Fin n) → ℝ := finiteMongeCost x y
  obtain ⟨π, hπ⟩ := Finite.exists_min cost
  exact ⟨π, hπ⟩
