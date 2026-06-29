import Mathlib

/-
TASK ID: prob_4_5
TYPE: Problem
SOURCE PLAN: 12_chap4_problems
TASK CONTENT:
\textbf{4.5.} Let $(\Omega, \mathcal{F})$ be a measurable space and $f_1, f_2, \dots, f_n$ are measurable functions from $(\Omega, \mathcal{F})$ to $(\mathbb{R}, \mathcal{B}(\mathbb{R}))$. Prove that for any continuous function $g : \mathbb{R}^n \to \mathbb{R}$, the function $g(f_1(\omega), f_2(\omega), \dots, f_n(\omega))$ is measurable with respect to the $\sigma$-algebra $\mathcal{F}$.
-/

-- WRITE FINAL LEAN CODE BELOW

theorem prob_4_5 (Ω : Type*) [MeasurableSpace Ω] (n : ℕ)
    (f : Fin n → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) :
    Measurable (fun ω => g (fun i => f i ω)) := by
  exact hg.measurable.comp (measurable_pi_lambda _ hf)
