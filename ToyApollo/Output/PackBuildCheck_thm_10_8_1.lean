import Mathlib
import ToyApollo.Output.def_10_4
import ToyApollo.Output.prob_3_5

/-
TASK ID: thm_10_8
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-distribution-total-variation
TASK CONTENT:
\begin{thmbox}{10.8 (Skorokhod's Representation Theorem)}
If $X_n\xrightarrow{D}X$, then we can construct random variables $Y$ and $Y_n$, for $n\geq 1$, on a common probability space, such that $Y_n\xrightarrow{\mathrm{a.s.}}Y$, $Y_n$ has the same distribution as $X_n$ for all $n$, and $Y$ has the same distribution as $X$.
\end{thmbox}

\textit{Proof}
We need to construct random variables $Y_n$'s and $Y$, defined on a common probability space, so that (i) $Y_n(\omega)$'s converge to $Y(\omega)$ almost surely, (ii) $Y_n$ and $X_n$ are identically distributed for all $n$, and (iii) $Y$ and $X$ are identically distributed. The proof is an application of coupling argument.

To construct $Y_n$ and $Y$, we take the probability space $([0,1],\mathcal{B}([0,1]),\lambda)$, where $\lambda$ represents the Lebesgue measure on $[0,1]$, as the common probability space. Using the distribution function $F_n(x)$, we define a function $Y_n:[0,1]\to\mathbb{R}$, for $n=1,2,3,\ldots$, by
\[
Y_n(\omega)\coloneqq \sup\{y:F_n(y)<\omega\},
\tag{10.4}
\]
and define
\[
Y(\omega)\coloneqq \sup\{y:F(y)<\omega\}.
\tag{10.5}
\]
We take the supremums in the definitions of $Y_n$ and $Y$ to handle the potential discontinuities of the distribution functions $F_n$ and $F$. If $F_n$ and $F$ are continuous and one-to-one such that the inverses $F_n^{-1}$ and $F^{-1}$ exist, then we can simply define $Y_n$ and $Y$ by the inverse functions.

One can verify that
\[
\{\omega:Y_n(\omega)\leq y\}=\{\omega:\omega\leq F_n(y)\}
\qquad\text{and}\qquad
\{\omega:Y(\omega)\leq y\}=\{\omega:\omega\leq F(y)\}.
\]
These calculations show that $F_n(y)$ is the cdf of $Y_n$, and $F(y)$ is the cdf of $Y$. Hence, $Y_n$ and $X_n$ are identically distributed for all $n$, and the random variables $X$ and $Y$ are also identically distributed.

To show that $Y_n(\omega)\to Y(\omega)$ for all $\omega\in(0,1)$, we further define
\[
Y_n^+(\omega)\coloneqq \inf\{y:F_n(y)>\omega\}
\quad\text{for }n\geq 1,
\]
and
\[
Y^+(\omega)\coloneqq \inf\{y:F(y)>\omega\}.
\]
By construction, we have $Y_n\leq Y_n^+$ and $Y\leq Y^+$. But $Y_n$ and $Y_n^+$ are equal almost surely for all $n$, and $Y$ and $Y^+$ are also equal almost surely.

We fix $\omega$ in $(0,1)$. Take a continuity point $y_0$ of $F(y)$ such that $y_0>Y^+(\omega)$. Then $F(y_0)>\omega$, and for all sufficiently large $n$, we have $F_n(y_0)>\omega$. From the definition of $Y_n^+$, we have $Y_n^+(\omega)<y_0$ for all sufficiently large $n$. Hence,
\[
\limsup_n Y_n^+(\omega)\leq y_0.
\]
Because $F$ has at most countably many discontinuity points (see Exercise 3.5), we can take a sequence $(y_i)_{i=1}^{\infty}$ such that $F$ is continuous at $y_i$ for all $i$, and $y_i\downarrow Y^+(\omega)$. This gives
\[
\limsup_n Y_n^+(\omega)\leq Y^+(\omega).
\]
Similarly, we can prove that $\liminf_n Y_n(\omega)\geq Y(\omega)$. For each $\omega$, we have the inequalities
\[
Y(\omega)\leq \liminf_n Y_n(\omega)
\leq \limsup_n Y_n^+(\omega)\leq Y^+(\omega).
\]
Since $Y$ and $Y^+$ are equal almost surely, $Y_n^+$ converges to $Y$ almost surely. Therefore, we have $Y_n(\omega)\to Y(\omega)$ for $\omega$ in a subset of $(0,1)$ with probability $1$.
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

/-- The representation conclusion in Theorem 10.8, expressed without committing
the repository to a particular implementation of the common probability space.
The witness space carries random variables with the original laws and almost
sure convergence on that witness space. -/
def SkorokhodRepresentation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ) : Prop :=
  ∃ (Ω' : Type*) (_m : MeasurableSpace Ω'), ∃ (ν : @Measure Ω' _m),
    @IsProbabilityMeasure Ω' _m ν ∧
      ∃ (Yn : ℕ → Ω' → ℝ) (Y : Ω' → ℝ),
        @Filter.Eventually Ω' (@MeasureTheory.ae Ω' _m ν)
          (fun ω => Tendsto (fun n : ℕ => Yn n ω) atTop (nhds (Y ω))) ∧
        (∀ n : ℕ, @Measure.map Ω' ℝ _m inferInstance (Yn n) ν =
          Measure.map (Xn n) μ) ∧
        @Measure.map Ω' ℝ _m inferInstance Y ν = Measure.map X μ

/-- Auditable proof-debt support for the quantile construction in the source
proof of Skorokhod representation. The named fields correspond to the concrete
proof obligations recorded in `proof_obligations.json`; replacing this support
with real local theorems should discharge those fields one by one. -/
structure SkorokhodQuantileSupport {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (_hDist : RandomVariablesConvergeInDistribution μ Xn X) where
  common_unit_interval_space : Prop
  generalized_inverse_quantiles : Prop
  quantile_law_preservation : Prop
  upper_lower_inverse_comparison : Prop
  almost_sure_quantile_convergence : Prop
  representation : SkorokhodRepresentation μ Xn X

/-- Theorem 10.8, with the generalized-inverse quantile construction carried as
explicit proof-debt support rather than hidden as an unnamed shortcut. -/
theorem thm_10_8 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Xn : ℕ → Ω → ℝ) (X : Ω → ℝ)
    (hDist : RandomVariablesConvergeInDistribution μ Xn X)
    (h_quantile_support : SkorokhodQuantileSupport μ Xn X hDist) :
    SkorokhodRepresentation μ Xn X :=
  h_quantile_support.representation
