/-
TASK ID: prob_2_10
TYPE: Problem
SOURCE PLAN: 45_chap2_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




 
def rationalOpenIntervals : Set (Set ℝ) :=
  {s : Set ℝ | ∃ (a b : ℚ), a < b ∧ s = Set.Ioo (a : ℝ) (b : ℝ)}

lemma rationalOpenIntervals_countable : Set.Countable rationalOpenIntervals := by
  refine (Set.countable_range
    (fun p : ℚ × ℚ => Set.Ioo (p.1 : ℝ) (p.2 : ℝ))).mono ?_
  rintro s ⟨a, b, _hab, rfl⟩
  exact ⟨(a, b), rfl⟩

lemma rationalOpenIntervals_eq_mathlib_generator :
    rationalOpenIntervals =
      (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Set.Ioo (a : ℝ) (b : ℝ)}) := by
  ext s
  simp [rationalOpenIntervals]

lemma borel_eq_generateFrom_rationalOpenIntervals :
    borel ℝ = MeasurableSpace.generateFrom rationalOpenIntervals := by
  rw [rationalOpenIntervals_eq_mathlib_generator]
  exact Real.borel_eq_generateFrom_Ioo_rat

theorem prob_2_10 :
    ∃ (𝒞 : Set (Set ℝ)), Set.Countable 𝒞 ∧
      borel ℝ = MeasurableSpace.generateFrom 𝒞 := by
  exact ⟨rationalOpenIntervals, rationalOpenIntervals_countable,
    borel_eq_generateFrom_rationalOpenIntervals⟩
