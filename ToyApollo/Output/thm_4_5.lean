/-
TASK ID: thm_4_5
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.thm_2_8
import ToyApollo.Output.thm_4_4

open MeasureTheory Set

def finOpenBalls (d : ℕ) : Set (Set (Fin d → ℝ)) :=
  {A | ∃ c : Fin d → ℝ, ∃ r : ℝ, 0 < r ∧ A = Metric.ball c r}

theorem finOpenBalls_generateFrom_eq_borel (d : ℕ) :
    MeasurableSpace.generateFrom (finOpenBalls d) = borel (Fin d → ℝ) := by
  simpa [finOpenBalls] using
    (metricOpenBalls_isTopologicalBasis (α := Fin d → ℝ)).borel_eq_generateFrom.symm

theorem continuous_preimage_finOpenBall_measurable {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (hf : Continuous f) :
    ∀ A ∈ finOpenBalls n, MeasurableSet (f ⁻¹' A) := by
  rintro A ⟨c, r, _hr, rfl⟩
  exact (Metric.isOpen_ball.preimage hf).measurableSet

theorem continuous_to_generated_finOpenBalls_measurable {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (hf : Continuous f) :
    @Measurable (Fin m → ℝ) (Fin n → ℝ) inferInstance
      (MeasurableSpace.generateFrom (finOpenBalls n)) f := by
  exact (thm_4_4 f).2 (continuous_preimage_finOpenBall_measurable f hf)

theorem continuous_to_borel_measurable {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (hf : Continuous f) :
    Measurable f := by
  have hgen :
      (inferInstance : MeasurableSpace (Fin n → ℝ)) =
        MeasurableSpace.generateFrom (finOpenBalls n) := by
    calc
      (inferInstance : MeasurableSpace (Fin n → ℝ)) = borel (Fin n → ℝ) :=
        BorelSpace.measurable_eq
      _ = MeasurableSpace.generateFrom (finOpenBalls n) :=
        (finOpenBalls_generateFrom_eq_borel n).symm
  have hsrc := continuous_to_generated_finOpenBalls_measurable f hf
  convert hsrc using 1

theorem continuous_preimage_borel {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (hf : Continuous f)
    (B : Set (Fin n → ℝ)) (hB : MeasurableSet B) :
    MeasurableSet (f ⁻¹' B) :=
  continuous_to_borel_measurable f hf hB

theorem continuous_real_valued_to_borel_measurable {m : ℕ}
    (f : (Fin m → ℝ) → ℝ) (hf : Continuous f) :
    Measurable f := by
  have hgen :
      (inferInstance : MeasurableSpace ℝ) =
        MeasurableSpace.generateFrom
          {A : Set ℝ | ∃ c : ℝ, ∃ r : ℝ, 0 < r ∧ A = Metric.ball c r} := by
    calc
      (inferInstance : MeasurableSpace ℝ) = borel ℝ := BorelSpace.measurable_eq
      _ = MeasurableSpace.generateFrom
          {A : Set ℝ | ∃ c : ℝ, ∃ r : ℝ, 0 < r ∧ A = Metric.ball c r} :=
          (metricOpenBalls_isTopologicalBasis (α := ℝ)).borel_eq_generateFrom
  have hsrc :
      @Measurable (Fin m → ℝ) ℝ inferInstance
        (MeasurableSpace.generateFrom
          {A : Set ℝ | ∃ c : ℝ, ∃ r : ℝ, 0 < r ∧ A = Metric.ball c r}) f := by
    exact (thm_4_4 f).2 (by
      rintro A ⟨c, r, _hr, rfl⟩
      exact (Metric.isOpen_ball.preimage hf).measurableSet)
  convert hsrc using 1

theorem continuous_euclidean_to_generated_openBalls_measurable {m n : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) :
    @Measurable (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)) inferInstance
      (MeasurableSpace.generateFrom (euclideanOpenBalls n)) f := by
  exact (thm_4_4 f).2 (by
    rintro A ⟨c, r, _hr, rfl⟩
    exact (Metric.isOpen_ball.preimage hf).measurableSet)

theorem continuous_euclidean_to_borel_measurable {m n : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) :
    Measurable f := by
  have hgen :
      (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))) =
        MeasurableSpace.generateFrom (euclideanOpenBalls n) := by
    calc
      (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))) =
          borel (EuclideanSpace ℝ (Fin n)) := BorelSpace.measurable_eq
      _ = MeasurableSpace.generateFrom (euclideanOpenBalls n) :=
          (euclideanOpenBalls_generateFrom_eq_borel n).symm
  have hsrc := continuous_euclidean_to_generated_openBalls_measurable f hf
  convert hsrc using 1

theorem thm_4_5 {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (hf : Continuous f) :
    Measurable f :=
  continuous_to_borel_measurable f hf
