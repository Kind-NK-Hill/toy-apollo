import Mathlib
import ToyApollo.Output.thm_13_5

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The dominating probability measure used in the proof of Theorem 14.4:
`ν = (P + Q) / 2`.  The scalar is written as `2⁻¹` in `ℝ≥0∞` so that
measure calculations stay in the native codomain of measures. -/
def thm_14_4_dominatingMeasure (P Q : ProbabilityMeasure ℝ) : Measure ℝ :=
  ((2 : ℝ≥0∞)⁻¹ • (P : Measure ℝ)) +
    ((2 : ℝ≥0∞)⁻¹ • (Q : Measure ℝ))

@[simp]
theorem thm_14_4_dominatingMeasure_apply
    (P Q : ProbabilityMeasure ℝ) (s : Set ℝ) :
    thm_14_4_dominatingMeasure P Q s =
      (2 : ℝ≥0∞)⁻¹ * (P : Measure ℝ) s +
        (2 : ℝ≥0∞)⁻¹ * (Q : Measure ℝ) s := by
  simp [thm_14_4_dominatingMeasure, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]

@[simp]
theorem thm_14_4_dominatingMeasure_univ
    (P Q : ProbabilityMeasure ℝ) :
    thm_14_4_dominatingMeasure P Q Set.univ = 1 := by
  simp [thm_14_4_dominatingMeasure, Measure.add_apply,
    Measure.smul_apply, ENNReal.inv_two_add_inv_two]

instance thm_14_4_dominatingMeasure_isProbabilityMeasure
    (P Q : ProbabilityMeasure ℝ) :
    IsProbabilityMeasure (thm_14_4_dominatingMeasure P Q) where
  measure_univ := thm_14_4_dominatingMeasure_univ P Q

/-- The left summand is absolutely continuous with respect to `(P + Q) / 2`. -/
theorem thm_14_4_left_absolutelyContinuous
    (P Q : ProbabilityMeasure ℝ) :
    (P : Measure ℝ) ≪ thm_14_4_dominatingMeasure P Q := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s _hs hs0
  have hsum :
      (2 : ℝ≥0∞)⁻¹ * (P : Measure ℝ) s +
          (2 : ℝ≥0∞)⁻¹ * (Q : Measure ℝ) s = 0 := by
    simpa using hs0
  have hleft :
      (2 : ℝ≥0∞)⁻¹ * (P : Measure ℝ) s = 0 :=
    (add_eq_zero.mp hsum).1
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hleft).resolve_left hhalf

/-- The right summand is absolutely continuous with respect to `(P + Q) / 2`. -/
theorem thm_14_4_right_absolutelyContinuous
    (P Q : ProbabilityMeasure ℝ) :
    (Q : Measure ℝ) ≪ thm_14_4_dominatingMeasure P Q := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s _hs hs0
  have hsum :
      (2 : ℝ≥0∞)⁻¹ * (P : Measure ℝ) s +
          (2 : ℝ≥0∞)⁻¹ * (Q : Measure ℝ) s = 0 := by
    simpa using hs0
  have hright :
      (2 : ℝ≥0∞)⁻¹ * (Q : Measure ℝ) s = 0 :=
    (add_eq_zero.mp hsum).2
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hright).resolve_left hhalf

/-- The sequence version of the dominating measure `ν_n = (μ_n + μ) / 2`. -/
def thm_14_4_dominatingMeasureSeq
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (n : ℕ) : Measure ℝ :=
  thm_14_4_dominatingMeasure (Pseq n) P

instance thm_14_4_dominatingMeasureSeq_isProbabilityMeasure
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (n : ℕ) :
    IsProbabilityMeasure (thm_14_4_dominatingMeasureSeq Pseq P n) := by
  dsimp [thm_14_4_dominatingMeasureSeq]
  infer_instance

theorem thm_14_4_mu_n_absolutelyContinuous
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (n : ℕ) :
    (Pseq n : Measure ℝ) ≪ thm_14_4_dominatingMeasureSeq Pseq P n := by
  dsimp [thm_14_4_dominatingMeasureSeq]
  exact thm_14_4_left_absolutelyContinuous (Pseq n) P

theorem thm_14_4_mu_absolutelyContinuous
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ)
    (n : ℕ) :
    (P : Measure ℝ) ≪ thm_14_4_dominatingMeasureSeq Pseq P n := by
  dsimp [thm_14_4_dominatingMeasureSeq]
  exact thm_14_4_right_absolutelyContinuous (Pseq n) P

/-- Radon-Nikodym density representation for both measures relative to
`ν_n = (μ_n + μ) / 2`. -/
theorem thm_14_4_rn_density_representation
    (Pseq : ℕ → ProbabilityMeasure ℝ) (P : ProbabilityMeasure ℝ) :
    ∀ n : ℕ,
      ∃ f : ℝ → ℝ≥0∞, ∃ g : ℝ → ℝ≥0∞,
        Measurable f ∧ Measurable g ∧
          (∀ ⦃B : Set ℝ⦄, MeasurableSet B →
            (Pseq n : Measure ℝ) B =
              ∫⁻ x in B, f x ∂thm_14_4_dominatingMeasureSeq Pseq P n) ∧
          (∀ ⦃B : Set ℝ⦄, MeasurableSet B →
            (P : Measure ℝ) B =
              ∫⁻ x in B, g x ∂thm_14_4_dominatingMeasureSeq Pseq P n) := by
  intro n
  let ν : Measure ℝ := thm_14_4_dominatingMeasureSeq Pseq P n
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν, thm_14_4_dominatingMeasureSeq]
    infer_instance
  have hPν : (Pseq n : Measure ℝ) ≪ ν := by
    dsimp [ν]
    exact thm_14_4_mu_n_absolutelyContinuous Pseq P n
  have hQν : (P : Measure ℝ) ≪ ν := by
    dsimp [ν]
    exact thm_14_4_mu_absolutelyContinuous Pseq P n
  refine ⟨(Pseq n : Measure ℝ).rnDeriv ν, (P : Measure ℝ).rnDeriv ν,
    Measure.measurable_rnDeriv _ _, Measure.measurable_rnDeriv _ _, ?_, ?_⟩
  · intro B hB
    simpa [ν] using thm_13_5_set_lintegral (Pseq n : Measure ℝ) ν hPν hB
  · intro B hB
    simpa [ν] using thm_13_5_set_lintegral (P : Measure ℝ) ν hQν hB

