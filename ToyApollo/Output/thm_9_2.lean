import Mathlib
import ToyApollo.Output.def_9_1
import ToyApollo.Output.def_9_2

/-
TASK ID: thm_9_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter9-moments-mgf
TASK CONTENT:
\begin{thmbox}{9.2}
If $X$ has moment generating function $M_X(t)$, then $X$ has finite moments of all orders, and they can be recovered from the moment generating function by
\[
\mathbb{E}[X^n] =
\left.\frac{d^n}{dt^n}M_X(t)\right|_{t=0}
\]
for $n=1,2,3,\ldots$.
\end{thmbox}

\textit{Proof}
In this proof we will use the inequality
\[
e^{\lvert tx\rvert} \leq e^{tx}+e^{-tx},
\]
which holds for any real numbers $t$ and $x$. By assumption, there exists $\delta>0$ such that $M_X(t)$ is finite for $-\delta<t<\delta$. Hence, $\mathbb{E}[e^{tX}]<\infty$ and $\mathbb{E}[e^{-tX}]<\infty$ for $\lvert t\rvert<\delta$.

We first prove that all moments of $X$ are finite using Taylor expansion. For any positive integer $n$, we have
\[
\frac{\lvert t\rvert^n}{n!}\lvert x\rvert^n \leq e^{\lvert tx\rvert},
\]
because the left-hand side is one of the terms in the power series expansion of $e^{\lvert tx\rvert}$, and all other terms in the expansion are positive. Substituting $t$ by $\delta/2$, we obtain
\[
\frac{(\delta/2)^n}{n!}\lvert x\rvert^n \leq e^{\delta\lvert x\rvert/2}.
\]
Since this holds for all $x$, we can replace $x$ by the random variable $X$ and take expectation on both sides. This gives
\[
\frac{(\delta/2)^n}{n!}\mathbb{E}[\lvert X\rvert^n]
\leq \mathbb{E}[e^{\delta\lvert X\rvert/2}],
\]
and therefore
\[
\mathbb{E}[\lvert X\rvert^n]
\leq n!\left(\frac{2}{\delta}\right)^n
\left(\mathbb{E}[e^{\delta X/2}]+\mathbb{E}[e^{-\delta X/2}]\right)
<\infty.
\]
Hence, by Theorem 6.6, the random variable $X^n$ is integrable for all $n$.

Next, from the Taylor expansion of the exponential function, we can derive the following inequality that holds for any real numbers $t$ and $x$, and for all positive integers $n$:
\[
\left\lvert \sum_{k=0}^{n}\frac{t^k}{k!}x^k \right\rvert
\leq \sum_{k=0}^{n}\frac{\lvert t\rvert^k}{k!}\lvert x\rvert^k
\leq e^{\lvert t\rvert\lvert x\rvert}.
\]
For each $t$ in the range $\lvert t\rvert<\delta$, the sum $\sum_{k=0}^{n}t^kX^k/k!$ is bounded by $e^{\lvert tX\rvert}$. On the other hand, $e^{\lvert tX\rvert}$ has finite expectation, because
\[
\mathbb{E}[e^{\lvert t\rvert\lvert X\rvert}]
\leq \mathbb{E}[e^{tX}]+\mathbb{E}[e^{-tX}]<\infty
\]
for all $\lvert t\rvert<\delta$. We can apply the dominated convergence theorem (Theorem 7.4) to obtain
\[
\mathbb{E}[e^{tX}]
= \mathbb{E}\left[\sum_{k=0}^{\infty}\frac{t^kX^k}{k!}\right]
= \sum_{i=0}^{\infty}\mathbb{E}\left[\frac{t^iX^i}{i!}\right]
= \sum_{i=0}^{\infty}\frac{\mathbb{E}[X^i]}{i!}t^i.
\]
Therefore, $M_X(t)$ can be expanded as a power series with radius of convergence $\delta$. Using the properties of power series, we see that $M_X(t)$ is infinitely differentiable and
\[
\left.\frac{d^n}{dt^n}M_X(t)\right|_{t=0} = \mathbb{E}[X^n].
\]
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory ProbabilityTheory

noncomputable def finiteMomentGeneratingFunction
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hXm : AEMeasurable X μ) (t : ℝ) : ℝ :=
  (momentGeneratingFunction μ X hXm t).toReal

theorem thm_9_2_integrable_exp_mul_of_momentGeneratingFunction_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    {t : ℝ} (ht : momentGeneratingFunction μ X hXm t < ⊤) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  exact (lintegral_ofReal_ne_top_iff_integrable
    (aemeasurable_exp_mul t hXm)
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)).1
    (by simpa [momentGeneratingFunction] using ht.ne)

theorem thm_9_2_finiteMomentGeneratingFunction_eq_mgf_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    {t : ℝ} (ht : Integrable (fun ω => Real.exp (t * X ω)) μ) :
    finiteMomentGeneratingFunction μ X hXm t = mgf X μ t := by
  have h_nonneg : 0 ≤ᵐ[μ] fun ω => Real.exp (t * X ω) :=
    Filter.Eventually.of_forall fun _ => Real.exp_nonneg _
  rw [finiteMomentGeneratingFunction, momentGeneratingFunction, mgf,
    ← ofReal_integral_eq_lintegral_ofReal ht h_nonneg]
  exact ENNReal.toReal_ofReal
    (integral_nonneg fun _ => Real.exp_nonneg _)

theorem thm_9_2_mem_interior_integrableExpSet_of_HasMomentGeneratingFunction
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    (hX : HasMomentGeneratingFunction μ X hXm) :
    (0 : ℝ) ∈ interior (integrableExpSet X μ) := by
  rcases hX with ⟨δ, hδ_pos, hδ_fin⟩
  rw [mem_interior]
  refine ⟨Set.Ioo (-δ) δ, ?_, isOpen_Ioo, ?_⟩
  · intro t ht
    exact thm_9_2_integrable_exp_mul_of_momentGeneratingFunction_lt_top hXm
      (hδ_fin t (abs_lt.mpr ht))
  · exact ⟨by linarith, hδ_pos⟩

theorem thm_9_2_finiteMomentGeneratingFunction_eq_mgf_near_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : AEMeasurable X μ)
    (hX : HasMomentGeneratingFunction μ X hXm) :
    finiteMomentGeneratingFunction μ X hXm =ᶠ[nhds (0 : ℝ)] mgf X μ := by
  have hInterior :
      (0 : ℝ) ∈ interior (integrableExpSet X μ) :=
    thm_9_2_mem_interior_integrableExpSet_of_HasMomentGeneratingFunction hXm hX
  filter_upwards [isOpen_interior.eventually_mem hInterior] with t ht
  have htSet : t ∈ integrableExpSet X μ :=
    (show interior (integrableExpSet X μ) ⊆ integrableExpSet X μ from
      interior_subset) ht
  exact thm_9_2_finiteMomentGeneratingFunction_eq_mgf_of_integrable hXm
    htSet

theorem thm_9_2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : AEMeasurable X μ) (hX : HasMomentGeneratingFunction μ X hXm) (n : ℕ) :
    Integrable (fun ω => X ω ^ n) μ ∧
      rthMoment μ X n =
        iteratedDeriv n (finiteMomentGeneratingFunction μ X hXm) 0 := by
  have hInterior :
      (0 : ℝ) ∈ interior (integrableExpSet X μ) :=
    thm_9_2_mem_interior_integrableExpSet_of_HasMomentGeneratingFunction hXm hX
  have hEvent :
      finiteMomentGeneratingFunction μ X hXm =ᶠ[nhds (0 : ℝ)] mgf X μ :=
    thm_9_2_finiteMomentGeneratingFunction_eq_mgf_near_zero hXm hX
  constructor
  · exact integrable_pow_of_mem_interior_integrableExpSet hInterior n
  · rw [Filter.EventuallyEq.iteratedDeriv_eq n hEvent]
    simpa [rthMoment, moment] using
      (iteratedDeriv_mgf_zero (X := X) (μ := μ) hInterior n).symm
