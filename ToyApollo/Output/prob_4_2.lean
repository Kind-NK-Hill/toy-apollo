/-
TASK ID: prob_4_2
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

theorem prob_4_2 {Ω : Type*} [MeasurableSpace Ω]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => |f x|) ∧
      Measurable (fun x => max (f x) (g x)) ∧
        Measurable (fun x => min (f x) (g x)) := by
  exact ⟨hf.norm, hf.max hg, hf.min hg⟩
