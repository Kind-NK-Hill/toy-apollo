/-
TASK ID: thm_7_9_value_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_7_9_filter_support

open Filter

noncomputable section

theorem thm_7_9_improperRSFilter_neBot : NeBot improperRSFilter := by
  exact improperRSFilter_neBot

theorem thm_7_9_improperRSIntegral_eq_of_convergesTo {g α : ℝ → ℝ} {I : ℝ}
    (h : ImproperRSConvergesTo g α I) :
    improperRSIntegral g α (thm_7_9_improperRSIntegrable_of_convergesTo h) = I := by
  simpa [thm_7_9_improperRSIntegrable_of_convergesTo] using
    (improperRSIntegral_eq_of_convergesTo h)

theorem thm_7_9_value_packaging_with_improperRSIntegral_spec {g α : ℝ → ℝ} {I : ℝ}
    (h : ImproperRSConvergesTo g α I) :
    ∃ hImp : ImproperRSIntegrable g α, I = improperRSIntegral g α hImp := by
  refine ⟨thm_7_9_improperRSIntegrable_of_convergesTo h, ?_⟩
  exact (thm_7_9_improperRSIntegral_eq_of_convergesTo h).symm
