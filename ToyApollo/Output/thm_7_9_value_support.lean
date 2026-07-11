import ToyApollo.Output.thm_7_9_filter_support

open Filter

noncomputable section

/-!
Value-recovery support for Theorem 7.9.

After another support step proves convergence to a concrete value, the local
Definition 1.4 interface chooses an improper integral value by `Classical.choose`.
This file owns the uniqueness step that recovers the concrete limit value from
`improperRSIntegral_spec`.
-/

theorem thm_7_9_improperRSFilter_neBot : NeBot improperRSFilter := by
  exact improperRSFilter_neBot

theorem thm_7_9_improperRSIntegral_eq_of_convergesTo {g α : ℝ → ℝ} {I : ℝ}
    (h : ImproperRSConvergesTo g α I) :
    improperRSIntegral g α (thm_7_9_improperRSIntegrable_of_convergesTo h) = I := by
  simpa [thm_7_9_improperRSIntegrable_of_convergesTo] using
    (improperRSIntegral_eq_of_convergesTo h)

/-- Package a concrete improper RS convergence value into the existential
shape used by Theorem 7.9's value conclusion. -/
theorem thm_7_9_value_packaging_with_improperRSIntegral_spec {g α : ℝ → ℝ} {I : ℝ}
    (h : ImproperRSConvergesTo g α I) :
    ∃ hImp : ImproperRSIntegrable g α, I = improperRSIntegral g α hImp := by
  refine ⟨thm_7_9_improperRSIntegrable_of_convergesTo h, ?_⟩
  exact (thm_7_9_improperRSIntegral_eq_of_convergesTo h).symm
