/-
TASK ID: chapter14_triangular_array_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




open Filter
open scoped BigOperators Topology

noncomputable section



structure chapter14_TriangularArrayNotation where
  rowLength : ℕ → ℕ
  rowLength_pos : ∀ n : ℕ, 0 < rowLength n
  variance : ∀ n : ℕ, Fin (rowLength n) → ℝ
  totalVariance : ℕ → ℝ
  totalVariance_eq :
    ∀ n : ℕ, totalVariance n = ∑ i : Fin (rowLength n), variance n i
  totalVariance_tendsto_atTop :
    Tendsto totalVariance atTop atTop
