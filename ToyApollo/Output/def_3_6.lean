import Mathlib.Data.Real.Basic

/-- A closed and bounded interval in ℝ is called a compact set in ℝ. -/
def IsCompactIntervalSet (s : Set ℝ) : Prop :=
  ∃ a b : ℝ, s = Set.Icc a b
