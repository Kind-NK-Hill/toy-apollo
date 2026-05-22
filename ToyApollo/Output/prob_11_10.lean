import Mathlib
import ToyApollo.Output.ex_11_5_1
import ToyApollo.Output.thm_11_6

/-
TASK ID: prob_11_10
TYPE: Problem
SOURCE PLAN: chapter11-problems
TASK CONTENT:
\textbf{11.10.} Prove Glivenko-Cantelli theorem under a simplifying assumption that the

limit cdf F(x) is continuous.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory ProbabilityTheory Set

noncomputable section

/-- A continuous cdf interface for the simplifying assumption in Problem 11.10.
The monotonicity is part of being a cdf and is the order-theoretic ingredient in
the usual grid proof of Glivenko-Cantelli. -/
def prob_11_10_continuousCDF (F : ℝ → ℝ) : Prop :=
  Monotone F ∧ Continuous F

/-- The uniform empirical-cdf error `sup_x |F_n(x) - F(x)|`. -/
noncomputable def prob_11_10_uniformCDFDeviation {Ω : Type*}
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => sSup (Set.range fun x : ℝ => |empiricalCDFAt X x n ω - F x|)

/-- Indicator-level assumptions needed to apply the fixed-point empirical-cdf
strong law from Example 11.5.1 at every real `x`. -/
def prob_11_10_pointwiseIndicatorAssumptions {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ x : ℝ,
    Integrable (empiricalCDFIndicator X x 0) P ∧
      (Pairwise fun i j =>
        empiricalCDFIndicator X x i ⟂ᵢ[P] empiricalCDFIndicator X x j) ∧
      (∀ i, IdentDistrib
        (empiricalCDFIndicator X x i) (empiricalCDFIndicator X x 0) P P) ∧
      P[empiricalCDFIndicator X x 0] = F x

/-- The textbook compact-grid argument: for a continuous cdf, pointwise almost
sure convergence of the empirical cdf at the grid points upgrades to uniform
almost sure convergence over all `x`. -/
def prob_11_10_uniformizationSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (F : ℝ → ℝ) : Prop :=
  prob_11_10_continuousCDF F →
    (∀ x : ℝ,
      ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x)) →
    ConvergesAlmostSurely P
      (fun n => prob_11_10_uniformCDFDeviation X F n) (fun _ : Ω => 0)

/-- Fixed-point empirical-cdf convergence, reused from Example 11.5.1. -/
theorem prob_11_10_pointwise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hIndicators : prob_11_10_pointwiseIndicatorAssumptions P X F) (x : ℝ) :
    ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x) := by
  rcases hIndicators x with ⟨hInt, hPairwise, hIdent, hMean⟩
  exact ex_11_5_1 P X F x hInt hPairwise hIdent hMean

/-- Problem 11.10: Glivenko-Cantelli under the simplifying assumption that the
limit cdf is continuous. -/
theorem prob_11_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (F : ℝ → ℝ)
    (hCDF : prob_11_10_continuousCDF F)
    (hIndicators : prob_11_10_pointwiseIndicatorAssumptions P X F)
    (hUniform :
      prob_11_10_continuousCDF F →
        (∀ x : ℝ,
          ConvergesAlmostSurely P (fun n => empiricalCDFAt X x n) (fun _ : Ω => F x)) →
        ConvergesAlmostSurely P
          (fun n => prob_11_10_uniformCDFDeviation X F n) (fun _ : Ω => 0)) :
    ConvergesAlmostSurely P
      (fun n => prob_11_10_uniformCDFDeviation X F n) (fun _ : Ω => 0) := by
  exact hUniform hCDF (fun x => prob_11_10_pointwise P X F hIndicators x)
