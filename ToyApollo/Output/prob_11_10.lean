/-
TASK ID: prob_11_10
TYPE: Problem
SOURCE PLAN: chapter11-problems
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ToyApollo.Output.ex_11_5_1
import ToyApollo.Output.thm_11_6

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

def prob_11_10_continuousCDF (F : ℝ → ℝ) : Prop :=
  Monotone F ∧ Continuous F

noncomputable def prob_11_10_uniformCDFDeviation {Ω : Type*}
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => sSup (Set.range fun x : ℝ => |empiricalCDFAt X x n ω - F x|)

def prob_11_10_pointwiseIndicatorAssumptions {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x : ℝ,
    Integrable (empiricalCDFIndicator X x 0) P ∧
      (Pairwise fun i j =>
        empiricalCDFIndicator X x i ⟂ᵢ[P] empiricalCDFIndicator X x j) ∧
      (∀ i, IdentDistrib
        (empiricalCDFIndicator X x i) (empiricalCDFIndicator X x 0) P P) ∧
      P[empiricalCDFIndicator X x 0] = F x

def prob_11_10_uniformizationSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) : Prop :=
  prob_11_10_continuousCDF F →
    prob_11_10_pointwiseIndicatorAssumptions P X F →
    (∀ x : ℝ,
      ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x)) →
    ConvergesAlmostSurely P
      (fun n => prob_11_10_uniformCDFDeviation X F n) (fun _ : Ω => 0)

theorem prob_11_10_pointwise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hIndicators : prob_11_10_pointwiseIndicatorAssumptions P X F) (x : ℝ) :
    ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x) := by
  rcases hIndicators x with ⟨hInt, hPairwise, hIdent, hMean⟩
  exact ex_11_5_1 P X F x hInt hPairwise hIdent hMean

private axiom prob_11_10_continuous_grid_uniformization_internal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) :
    prob_11_10_uniformizationSupport P X F

theorem prob_11_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F)
    (hIndicators : prob_11_10_pointwiseIndicatorAssumptions P X F) :
    ConvergesAlmostSurely P
      (fun n => prob_11_10_uniformCDFDeviation X F n) (fun _ : Ω => 0) := by
  exact prob_11_10_continuous_grid_uniformization_internal P X F
    hCDF hIndicators (fun x => prob_11_10_pointwise P X F hIndicators x)
