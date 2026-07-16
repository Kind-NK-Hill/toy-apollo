import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Bounded

open Set Metric Bornology

namespace Def36

/-- Textbook compactness for subsets of `ℝ`: closed and bounded. -/
def IsCompactTextbook (A : Set ℝ) : Prop :=
  IsClosed A ∧ IsBounded A

/-- A closed bounded interval is the interval-shaped instance of textbook compactness. -/
def IsCompactIntervalSet (A : Set ℝ) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ A = Set.Icc a b

theorem isCompactTextbook_of_compactInterval
    {A : Set ℝ} (hA : IsCompactIntervalSet A) : IsCompactTextbook A := by
  rcases hA with ⟨a, b, _hab, rfl⟩
  exact ⟨isClosed_Icc, Metric.isBounded_Icc a b⟩

end Def36

/-- Definition 3.6: a subset of `ℝ` is compact when it is closed and bounded. -/
def def_3_6 (A : Set ℝ) : Prop :=
  Def36.IsCompactTextbook A
