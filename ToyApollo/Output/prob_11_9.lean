/-
TASK ID: prob_11_9
TYPE: Problem
SOURCE PLAN: chapter11-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.def_10_3
import ToyApollo.Output.thm_10_5
import ToyApollo.Output.thm_11_2

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory

noncomputable section

noncomputable def prob_11_9_emptyBoxRatio {Ω : Type*}
    (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun n ω => X n ω / (boxes n : ℝ)

def prob_11_9_asymptoticRegime (boxes k : ℕ → ℕ) (a : ℝ) : Prop :=
  (∀ n : ℕ, 0 < boxes n) ∧
    Tendsto (fun n : ℕ => (boxes n : ℝ)) atTop atTop ∧
    0 < a ∧
    Tendsto (fun n : ℕ => (k n : ℝ) / (boxes n : ℝ)) atTop (nhds a)

def prob_11_9_occupancyMomentSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ) : Prop :=
  prob_11_9_asymptoticRegime boxes k a →
    Tendsto
      (fun n : ℕ =>
        meanDeviationMoment P (prob_11_9_emptyBoxRatio boxes X)
          (fun _ : Ω => Real.exp (-a)) 2 n)
      atTop (nhds 0)

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
  rcases hMS with ⟨_hTwo, hTendsto⟩
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

private theorem prob_11_9_quadratic_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hMoment : prob_11_9_occupancyMomentSupport P boxes k X a) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) := by
  refine ⟨by norm_num, ?_⟩
  exact hMoment hRegime

private theorem prob_11_9_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (boxes : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hMS : ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)))
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
      (fun _ : Ω => Real.exp (-a)) := by
  let hELp := prob_11_9_meanSquareELpNormSupport_of_measurable P boxes X a hX
  rcases hELp hMS with ⟨hX, hLimit, hLp⟩
  exact thm_10_5 P (prob_11_9_emptyBoxRatio boxes X)
    (fun _ : Ω => Real.exp (-a)) (p := (2 : ENNReal)) (by norm_num) hX hLimit hLp

theorem prob_11_9 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (boxes k : ℕ → ℕ) (X : ℕ → Ω → ℝ) (a : ℝ)
    (hRegime : prob_11_9_asymptoticRegime boxes k a)
    (hMoment :
      prob_11_9_asymptoticRegime boxes k a →
        Tendsto
          (fun n : ℕ =>
            meanDeviationMoment P (prob_11_9_emptyBoxRatio boxes X)
              (fun _ : Ω => Real.exp (-a)) 2 n)
          atTop (nhds 0))
    (hX :
      ∀ n : ℕ, AEStronglyMeasurable ((prob_11_9_emptyBoxRatio boxes X) n) P) :
    ConvergesInMeanSquare P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) ∧
      ConvergesInProbability P (prob_11_9_emptyBoxRatio boxes X)
        (fun _ : Ω => Real.exp (-a)) := by
  have hMomentSupport : prob_11_9_occupancyMomentSupport P boxes k X a := by
    simpa [prob_11_9_occupancyMomentSupport] using hMoment
  let hMS := prob_11_9_quadratic_mean P boxes k X a hRegime hMomentSupport
  exact ⟨hMS, prob_11_9_probability P boxes X a hMS hX⟩
