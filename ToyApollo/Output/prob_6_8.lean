import Mathlib

/-
TASK ID: prob_6_8
TYPE: Problem
SOURCE PLAN: 24_chap6_problems
TASK CONTENT:
\textbf{6.8.} Let $(\Omega,\mathcal{F},\mu)$ be a measure space and $X$ be a nonnegative measurable function defined on this measure space such that $\int_{\Omega} X\, d\mu =1$. Prove that the set function $Q$, defined by $Q(A)=\int_A X\, d\mu$ for $A\in\mathcal{F}$, is a probability measure.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

theorem prob_6_8 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ENNReal)
    (hX : Measurable X) (hint : ∫⁻ ω, X ω ∂μ = 1) : IsProbabilityMeasure (μ.withDensity X) := by
  constructor
  aesop
