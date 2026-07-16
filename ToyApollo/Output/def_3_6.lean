/-
TASK ID: def_3_6
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric Bornology

namespace Def36

def IsCompactTextbook (A : Set ℝ) : Prop :=
  IsClosed A ∧ IsBounded A

def IsCompactIntervalSet (A : Set ℝ) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ A = Set.Icc a b

theorem isCompactTextbook_of_compactInterval
    {A : Set ℝ} (hA : IsCompactIntervalSet A) : IsCompactTextbook A := by
  rcases hA with ⟨a, b, _hab, rfl⟩
  exact ⟨isClosed_Icc, Metric.isBounded_Icc a b⟩

end Def36

def def_3_6 (A : Set ℝ) : Prop :=
  Def36.IsCompactTextbook A
