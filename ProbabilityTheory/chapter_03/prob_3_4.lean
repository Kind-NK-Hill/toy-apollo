/-
TASK ID: prob_3_4
TYPE: Problem
SOURCE PLAN: 07_chap3_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib




-- WRITE FINAL LEAN CODE BELOW

theorem prob_3_4 (F1 F2 : StieltjesFunction ℝ)
    (h : F1.measure = F2.measure) :
    ∃ (c : ℝ), ∀ (x : ℝ), F1 x = F2 x + c := by
  -- Equal Stieltjes measures have equal masses on every interval `(a, b]`,
  -- hence equal increments of the corresponding Stieltjes functions.
  have h_eq_zero : ∀ (a b : ℝ) (hab : a < b), F1 b - F1 a = F2 b - F2 a := by
    intro a b hab
    have h_interval : F1.measure (Set.Ioc a b) = F2.measure (Set.Ioc a b) := by
      simpa using congr_arg (fun μ : MeasureTheory.Measure ℝ => μ (Set.Ioc a b)) h
    rw [F1.measure_Ioc a b, F2.measure_Ioc a b] at h_interval
    exact (ENNReal.ofReal_eq_ofReal_iff
      (sub_nonneg_of_le <| F1.mono' hab.le)
      (sub_nonneg_of_le <| F2.mono' hab.le)).mp h_interval
  refine ⟨F1 0 - F2 0, ?_⟩
  intro x
  obtain hx | rfl | hx := lt_trichotomy x 0
  · have h_inc := h_eq_zero x 0 hx
    linarith
  · ring
  · have h_inc := h_eq_zero 0 x hx
    linarith
