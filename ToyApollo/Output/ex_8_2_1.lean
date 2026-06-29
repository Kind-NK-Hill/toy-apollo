import Mathlib
import ToyApollo.Output.thm_8_2

/-
TASK ID: ex_8_2_1
TYPE: Example_Proof
SOURCE PLAN: 32_chap8_product_measure_fubini
TASK CONTENT:
\textbf{Example 8.2.1 (The Product of a Discrete and a Continuous Distribution)} \\
Using Theorem 8.2, we are able to construct the product measure of two probability distributions of different types. Suppose $(\mathbb{R},\mathcal{B}(\mathbb{R}),P)$ represents a Poisson distribution with mean $\lambda$, and $(\mathbb{R},\mathcal{B}(\mathbb{R}),Q)$ represents Gaussian distribution with zero mean and unit variance. In this example, the product $\sigma$-algebra $\mathcal{B}(\mathbb{R})\times \mathcal{B}(\mathbb{R})$ is the same as $\mathcal{B}(\mathbb{R}^2)$. Let $P\times Q$ be the product measure. We can calculate the probability of the event $\{n\}\times [a,b]$, where $n$ is a positive integer and $a<b$ are real numbers,
\[
(P\times Q)(\{n\}\times [a,b])
=
\frac{\lambda^n}{n!}e^{-\lambda}
\int_a^b \frac{1}{\sqrt{2\pi}}e^{-x^2/2}\, dx.
\]

The probability in this example is concentrated on $\{0,1,2,\dots\}\times \mathbb{R}$.

Once we have the product measure on the product space, we can compute the Lebesgue integral on it. One useful method for doing so is through iterative integration, which involves integrating with respect to one variable at a time. The Tonelli and Fubini theorems are mathematical tools that enable this approach. Before we state these two theorems, it is helpful to first consider a counter-example that motivates the need for these theorems.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory Set

noncomputable section

/-- Example 8.2.1: the product of a Poisson law and a standard Gaussian assigns to the rectangle
`{n} × [a,b]` the product of the singleton Poisson mass and the Gaussian interval mass. -/
theorem ex_8_2_1 (r : NNReal) (n : ℕ) (a b : ℝ) :
    ((poissonMeasure r).prod (gaussianReal (0 : ℝ) (1 : NNReal))) ({n} ×ˢ Set.Icc a b) =
      ENNReal.ofReal
        (poissonPMFReal r n * ∫ x in Set.Icc a b, gaussianPDFReal (0 : ℝ) (1 : NNReal) x) := by
  have hprod :
      ((poissonMeasure r).prod (gaussianReal (0 : ℝ) (1 : NNReal))) ({n} ×ˢ Set.Icc a b) =
        (poissonMeasure r) {n} * (gaussianReal (0 : ℝ) (1 : NNReal)) (Set.Icc a b) := by
    simpa using
      (Measure.prod_prod
        (μ := poissonMeasure r)
        (ν := gaussianReal (0 : ℝ) (1 : NNReal))
        ({n} : Set ℕ)
        (Set.Icc a b))
  rw [hprod]
  unfold poissonMeasure
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]
  rw [gaussianReal_apply_eq_integral (μ := (0 : ℝ)) (v := (1 : NNReal)) (hv := by norm_num)]
  rw [← poissonPMFReal_ofReal_eq_poissonPMF]
  rw [← ENNReal.ofReal_mul (poissonPMFReal_nonneg)]
