/-
TASK ID: prob_9_3
TYPE: Problem
SOURCE PLAN: chapter9-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_09.prob_9_3_proof_support




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section



theorem prob_9_3
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    {X Y : Omega -> ℝ} {alpha1 alpha2 beta : ℝ}
    (halpha1 : 0 < alpha1) (halpha2 : 0 < alpha2) (hbeta : 0 < beta)
    (hX : HasSourceScaleGammaLaw P X alpha1 beta)
    (hY : HasSourceScaleGammaLaw P Y alpha2 beta)
    (hXY : X ⟂ᵢ[P] Y) :
    HasSourceScaleGammaLaw P (fun omega => X omega + Y omega)
      (alpha1 + alpha2) beta :=
  prob_9_3_support_result halpha1 halpha2 hbeta hX hY hXY
