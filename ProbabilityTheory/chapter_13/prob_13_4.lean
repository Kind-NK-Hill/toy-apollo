/-
TASK ID: prob_13_4
TYPE: Problem
SOURCE PLAN: chapter13-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_13.prob_13_4_support




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section



theorem prob_13_4 {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hXmeas : Measurable X) (hYmeas : Measurable Y)
    (hVarY : Var[Y; P] ≠ 0) :
    def_13_4 P Y (def_13_4_sigma_subSigma_of_measurable hYmeas) X
      (fun ω => (∫ ω, X ω ∂P) + (cov[X, Y; P] / Var[Y; P]) *
        (Y ω - ∫ ω, Y ω ∂P)) :=
  prob_13_4_jointlyGaussian_affine_condExp_regression hXY hXmeas hYmeas hVarY
