/-
TASK ID: prob_11_9_probability_support
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ProbabilityTheory.chapter_11.prob_11_9_limit_support

open Filter MeasureTheory ProbabilityTheory

noncomputable section

open scoped BigOperators



def prob_11_9_meanSquareELpNormSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ) : Prop :=
  ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) →
    (∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) ∧
      AEStronglyMeasurable (fun _ : Ω => Real.exp (-a)) P ∧
      Tendsto
        (fun n : ℕ =>
          eLpNorm
            (((prob_11_9_emptyBoxRatio boxes X) n) - fun _ : Ω => Real.exp (-a))
            (2 : ENNReal) P)
        atTop (nhds 0)



theorem prob_11_9_eLpNorm_tendsto_of_convergesInMeanSquare
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hMS : ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a))) :
    Tendsto
      (fun n : ℕ =>
        eLpNorm
          (((prob_11_9_emptyBoxRatio boxes X) n) -
            fun _ : Ω => Real.exp (-a))
          (2 : ENNReal) P)
      atTop (nhds 0) := by
  rcases hMS with ⟨_hX, _hLimit, _hTwo, hTendsto⟩
  have hroot :
      Tendsto (fun y : ENNReal => y ^ (1 / (2 : ℝ))) (nhds 0) (nhds 0) := by
    simpa using
      (ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ)))).tendsto 0
  have hcomp := hroot.comp hTendsto
  convert hcomp using 1
  ext n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  congr with ω
  rw [Real.enorm_eq_ofReal_abs]
  norm_num
  rw [← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]



theorem prob_11_9_meanSquareELpNormSupport_of_measurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    prob_11_9_meanSquareELpNormSupport P boxes X a := by
  intro hMS
  exact ⟨hX, aestronglyMeasurable_const,
    prob_11_9_eLpNorm_tendsto_of_convergesInMeanSquare P boxes X a hMS⟩



theorem prob_11_9_quadratic_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hModel : prob_11_9_finiteIndependentUniformEmptyBoxModel P boxes k X)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) := by
  let momentTendsto :=
    prob_11_9_occupancy_moment_calculation_internal P boxes k X a hModel
      hRegime hX
  exact ⟨hX, aestronglyMeasurable_const, by norm_num, momentTendsto⟩



theorem prob_11_9_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hMS : ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)))
    (hX :
      ∀ n : ℕ, Measurable ((prob_11_9_emptyBoxRatio boxes X) n)) :
    ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) := by
  exact thm_10_5 P (prob_11_9_emptyBoxRatio boxes X)
    (fun _ : Ω => Real.exp (-a)) (r := 2) hX measurable_const hMS

 
theorem prob_11_9_hence_in_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hMS : ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)))
    (hX :
      ∀ n : ℕ, Measurable ((prob_11_9_emptyBoxRatio boxes X) n)) :
    ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) :=
  prob_11_9_probability P boxes X a hMS hX
