/-
TASK ID: thm_14_7
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter14-central-limit-theorems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_14.thm_14_7_support




-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section



theorem thm_14_7_weakLimit_by_Levy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P)
    (hIntegrable : Integrable (X 0) P)
    (hSquareIntegrable : Integrable (fun ω => (X 0 ω) ^ 2) P)
    (hMean : P[X 0] = mu)
    (hVariance : ProbabilityTheory.variance (X 0) P = sigma ^ 2)
    (hsigma : 0 < sigma) :
    thm_14_1_weakLimit (thm_14_7_standardizedSumLaws P X mu sigma hX) := by
  have hChar :=
    thm_14_7_pointwiseCharacteristicConvergence
      P X mu sigma hX hIndep hIdent hIntegrable hSquareIntegrable hMean
      hVariance hsigma
  have hLimit :
      thm_14_1_limitIsCharacteristic thm_14_7_standardNormalCharacteristic := by
    refine ⟨thm_14_7_standardNormalLaw, ?_⟩
    intro t
    exact (thm_14_7_standardNormalLaw_characteristic t).symm
  exact (thm_14_1_weak_iff_characteristic hChar).2 hLimit



theorem thm_14_7
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (mu sigma : ℝ)
    (hX : ∀ k : ℕ, AEMeasurable (X k) P)
    (hIndep : ProbabilityTheory.iIndepFun X P)
    (hIdent : ∀ k : ℕ, IdentDistrib (X k) (X 0) P P)
    (hIntegrable : Integrable (X 0) P)
    (hSquareIntegrable : Integrable (fun ω => (X 0 ω) ^ 2) P)
    (hMean : P[X 0] = mu)
    (hVariance : ProbabilityTheory.variance (X 0) P = sigma ^ 2)
    (hsigma : 0 < sigma) :
    Tendsto (thm_14_7_standardizedSumLaws P X mu sigma hX)
      atTop (𝓝 thm_14_7_standardNormalLaw) :=
by
  have hChar :=
    thm_14_7_pointwiseCharacteristicConvergence
      P X mu sigma hX hIndep hIdent hIntegrable hSquareIntegrable hMean
      hVariance hsigma
  refine
    (MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun
      (μ := thm_14_7_standardizedSumLaws P X mu sigma hX)
      (μ₀ := thm_14_7_standardNormalLaw)).2 ?_
  intro t
  have hStandard :
      charFun ((thm_14_7_standardNormalLaw : ProbabilityMeasure ℝ) : Measure ℝ) t =
        thm_14_7_standardNormalCharacteristic t := by
    simpa [thm_14_1_characteristicFunction] using
      thm_14_7_standardNormalLaw_characteristic t
  rw [hStandard]
  exact hChar t
