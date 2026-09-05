/-
TASK ID: thm_14_5
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-tightness
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_14.thm_14_5_support




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set Complex Real
open scoped Topology RealInnerProductSpace ENNReal

noncomputable section



theorem thm_14_5
    (Pseq : ℕ → ProbabilityMeasure ℝ) (c : ℝ → ℂ)
    (hchar : thm_14_5_characteristicConvergence Pseq c)
    (hcont : ContinuousAt c 0) :
    def_14_3 Pseq := by
  exact
    thm_14_5_of_uniformTailBound Pseq
      (thm_14_5_source_route_uniform_tail_bound Pseq c hchar hcont)
