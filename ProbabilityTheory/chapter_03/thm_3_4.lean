/-
TASK ID: thm_3_4
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Bounded




open Set Metric Bornology



def IsCompactTextbook (A : Set ℝ) : Prop :=
  IsClosed A ∧ IsBounded A



theorem heine_borel (A : Set ℝ) :
    IsCompactTextbook A ↔
    (∀ {ι : Type} (U : ι → Set ℝ), (∀ i, IsOpen (U i)) → (A ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i) := by
  -- 1. Unfold our textbook definition of compactness
  rw [IsCompactTextbook]
  -- 2. Use the Heine-Borel theorem for proper spaces (like ℝ)
  -- to relate Closed + Bounded to Mathlib's IsCompact
  rw [← Metric.isCompact_iff_isClosed_bounded]
  -- 3. Use the topological definition of IsCompact to relate it to
  -- the finite subcover property
  exact isCompact_iff_finite_subcover
