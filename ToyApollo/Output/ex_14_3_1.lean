import Mathlib
import ToyApollo.Output.thm_14_1

/-
TASK ID: ex_14_3_1
TYPE: Example_Proof
SOURCE PLAN: chapter14-prokhorov-sequential-compactness
TASK CONTENT:
\textbf{Example 14.3.1 (Binomial Converging to Poisson)} \\

Let Xn be a random variable with binomial distribution Bin(n, pn) with pn =\lambda/n ,f o rafi x e d

positive constant. \lambda. The characteristic function of. Xn is

\phiXn (t)= ( 1- p n +p neit )n.

If we taken\to\infty ,

limn\to\infty \phiXn (t)= limn\to\infty

(

1- \lambda

n(1- e it )

) n

=e \lambda(eit -1),

which is the characteristic function of a Poisson random variable. By Theorem 14.1,Xn converges

to a Poisson random variable with mean. \lambda in distribution.
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory
open scoped Topology

noncomputable section

/-- The binomial success probability used in the example, indexed by `n + 1`
so the Lean sequence starts at `0` while the textbook sequence starts at
positive `n`. -/
def ex_14_3_1_pn (lam : ℝ) (n : ℕ) : ℝ :=
  lam / (n + 1 : ℝ)

/-- The characteristic function formula for `Bin(n + 1, λ/(n + 1))` in the
textbook form after rewriting `1 - p + p e^{it}`. -/
def ex_14_3_1_binomialCharacteristic
    (lam : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (1 + ((lam : ℂ) * (Complex.exp (Complex.I * (t : ℂ)) - 1)) /
      ((n : ℂ) + 1)) ^ (n + 1)

/-- The same binomial characteristic function in the displayed source form
`(1 - (λ/n)(1 - e^{it}))^n`, with `n` represented as `n + 1`. -/
theorem ex_14_3_1_binomialCharacteristic_source_form
    (lam : ℝ) (n : ℕ) (t : ℝ) :
    ex_14_3_1_binomialCharacteristic lam n t =
      (1 - ((lam : ℂ) / ((n : ℂ) + 1)) *
          (1 - Complex.exp (Complex.I * (t : ℂ)))) ^ (n + 1) := by
  unfold ex_14_3_1_binomialCharacteristic
  congr 1
  ring

/-- The characteristic function of the Poisson law with mean `λ`, as displayed
in the example. -/
def ex_14_3_1_poissonCharacteristic (lam : ℝ) (t : ℝ) : ℂ :=
  Complex.exp ((lam : ℂ) * (Complex.exp (Complex.I * (t : ℂ)) - 1))

/-- The analytic limit in the example:
`(1 + λ(e^{it}-1)/(n+1))^(n+1) → exp(λ(e^{it}-1))`. -/
theorem ex_14_3_1_binomialCharacteristic_tendsto
    (lam : ℝ) (t : ℝ) :
    Tendsto (fun n : ℕ => ex_14_3_1_binomialCharacteristic lam n t)
      atTop (𝓝 (ex_14_3_1_poissonCharacteristic lam t)) := by
  let z : ℂ := (lam : ℂ) * (Complex.exp (Complex.I * (t : ℂ)) - 1)
  have h :=
    (Complex.tendsto_one_add_div_pow_exp z).comp
      (tendsto_add_atTop_nat 1)
  change
    Tendsto (fun n : ℕ => (1 + z / ((n : ℂ) + 1)) ^ (n + 1))
      atTop (𝓝 (Complex.exp z))
  refine h.congr' ?_
  filter_upwards with n
  simp [Nat.cast_add, Nat.cast_one]

/-- A source-level package for the two laws in the example: the binomial laws
have the displayed characteristic functions and the limiting law has the
Poisson characteristic function with mean `λ`. -/
structure ex_14_3_1_BinomialPoissonSetup (lam : ℝ) where
  positive_lambda : 0 < lam
  binomialLaws : ℕ → ProbabilityMeasure ℝ
  poissonLaw : ProbabilityMeasure ℝ
  binomial_characteristic :
    ∀ n : ℕ, ∀ t : ℝ,
      thm_14_1_characteristicFunction (binomialLaws n) t =
        ex_14_3_1_binomialCharacteristic lam n t
  poisson_characteristic :
    ∀ t : ℝ,
      thm_14_1_characteristicFunction poissonLaw t =
        ex_14_3_1_poissonCharacteristic lam t

/-- The pointwise convergence hypothesis required by Theorem 14.1, obtained
from the displayed binomial characteristic function limit. -/
theorem ex_14_3_1_pointwiseCharacteristicConvergence
    {lam : ℝ} (S : ex_14_3_1_BinomialPoissonSetup lam) :
    thm_14_1_pointwiseCharFunConvergence S.binomialLaws
      (fun t : ℝ => thm_14_1_characteristicFunction S.poissonLaw t) := by
  intro t
  have hlimit := ex_14_3_1_binomialCharacteristic_tendsto lam t
  have hleft :
      (fun n : ℕ =>
        thm_14_1_characteristicFunction (S.binomialLaws n) t) =
        fun n : ℕ => ex_14_3_1_binomialCharacteristic lam n t := by
    funext n
    simpa using S.binomial_characteristic n t
  have hright :
      ex_14_3_1_poissonCharacteristic lam t =
        thm_14_1_characteristicFunction S.poissonLaw t :=
    (S.poisson_characteristic t).symm
  simpa [hleft, hright] using hlimit

/-- Applying the characteristic-function direction behind Theorem 14.1 gives
weak convergence of the binomial laws to the Poisson law. -/
theorem ex_14_3_1_converges_to_poisson
    {lam : ℝ} (S : ex_14_3_1_BinomialPoissonSetup lam) :
    Tendsto S.binomialLaws atTop (𝓝 S.poissonLaw) := by
  have hchar := ex_14_3_1_pointwiseCharacteristicConvergence S
  exact (ProbabilityMeasure.tendsto_iff_tendsto_charFun).2 (fun t : ℝ => by
    simpa [thm_14_1_characteristicFunction] using hchar t)

/-- The same conclusion in the existential weak-limit form exported by
Theorem 14.1. -/
theorem ex_14_3_1_weakLimit_by_Levy
    {lam : ℝ} (S : ex_14_3_1_BinomialPoissonSetup lam) :
    thm_14_1_weakLimit S.binomialLaws := by
  have hchar := ex_14_3_1_pointwiseCharacteristicConvergence S
  exact (thm_14_1_weak_iff_characteristic hchar).2
    ⟨S.poissonLaw, fun _ => rfl⟩

/-- Example 14.3.1: binomial laws `Bin(n, λ/n)` converge in distribution to
the Poisson law with mean `λ`, via characteristic functions and Theorem 14.1. -/
theorem ex_14_3_1
    {lam : ℝ} (S : ex_14_3_1_BinomialPoissonSetup lam) :
    Tendsto S.binomialLaws atTop (𝓝 S.poissonLaw) :=
  ex_14_3_1_converges_to_poisson S
