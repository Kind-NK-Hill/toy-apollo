/-
TASK ID: thm_7_9_bounded_finite_bridge_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.thm_7_8_ioc_bounded_bridge_support
import ToyApollo.Output.thm_7_9_endpoint_support

open MeasureTheory Set

noncomputable section

theorem thm_7_9_Icc_eq_endpoint_add_rs_of_bounded_measurableOn
    (F : StieltjesFunction ℝ) {a b : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b)
    (hIcc : IntegrableOn g (Icc a b) F.measure)
    (hgMeas : Measurable ((Icc a b).restrict g))
    (hAbove : BddAbove (g '' Icc a b))
    (hBelow : BddBelow (g '' Icc a b))
    (hRS : RSIntegrable g F a b) :
    IntegrableOn g (Icc a b) F.measure ∧
      IntegrableOn g (Ioc a b) F.measure ∧
      (∫ x in Icc a b, g x ∂F.measure =
        (F.measure {a}).toReal * g a + ∫ x in Ioc a b, g x ∂F.measure) ∧
      ∃ hRS' : RSIntegrable g F a b,
        ∫ x in Icc a b, g x ∂F.measure =
          (F.measure {a}).toReal * g a + rsIntegral g F a b hRS' := by
  have hEndpoint :
      ∫ x in Icc a b, g x ∂F.measure =
        (F.measure {a}).toReal * g a + ∫ x in Ioc a b, g x ∂F.measure :=
    thm_7_9_integral_Icc_eq_singleton_add_Ioc F hab hIcc
  have hIoc :=
    thm_7_8_ioc_bridge_of_rs_integrable_bounded_measurableOn
      F hgMeas hAbove hBelow hRS
  refine ⟨hIcc, hIoc.1, hEndpoint, ?_⟩
  rcases hIoc.2 with ⟨hRS', hIocEq⟩
  refine ⟨hRS', ?_⟩
  rw [hEndpoint, hIocEq]
