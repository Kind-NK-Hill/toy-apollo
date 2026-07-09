/-
TASK ID: thm_1_1
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_1_1_finite_discontinuity_support

open Finset BigOperators
open MeasureTheory Set Topology

noncomputable section

theorem thm_1_1
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : Monotone α)
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b → ContinuousAt α x) :
    RSIntegrable f α a b :=
  Thm11SourceRoute.strict_thm_1_1
    hab hα_mono hAbove hBelow hDiscFinite hαCont
