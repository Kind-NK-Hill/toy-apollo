/-
TASK ID: ex_14_4_1
TYPE: Example_Proof
SOURCE PLAN: chapter14-central-limit-theorems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_14.ex_14_4_1_proof_support




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section



theorem ex_14_4_1
    {Ω : Type*} [MeasurableSpace Ω]
    (S : ex_14_4_1_BernoulliSourceSetup Ω)
    (hSource : ex_14_4_1_bernoulliSourceLaw S) :
    Tendsto (ex_14_4_1_standardizedBinomialLaws S)
      atTop (𝓝 thm_14_7_standardNormalLaw) := by
  simpa using ex_14_4_1_support_result S hSource
