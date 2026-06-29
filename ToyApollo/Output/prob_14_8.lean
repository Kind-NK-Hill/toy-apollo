/-
TASK ID: prob_14_8
TYPE: Problem
SOURCE PLAN: chapter14-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.prob_14_8_proof_support

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology Uniformity

noncomputable section

theorem prob_14_8
    (S : prob_14_8_MgfConvergenceSetup) :
    def_14_3 S.laws ∧ Tendsto S.laws atTop (𝓝 S.targetLaw) := by
  simpa using prob_14_8_support_result S
