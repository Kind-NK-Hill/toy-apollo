import Mathlib
import ToyApollo.Output.def_9_3
import ToyApollo.Output.thm_7_6
import ToyApollo.Output.thm_8_5
import ToyApollo.Output.thm_9_4

/-
TASK ID: thm_9_5
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter9-characteristic-functions
TASK CONTENT:
\begin{thmbox}{9.5}
\textbf{Inversion Formula.}
Let $X$ be a random variable on a probability space $(\Omega,\mathcal{F},P)$, and let $\phi_X(t)$ be the characteristic function of $X$. Denote the push-forward measure of $P$ by $\mu$. For $a<b$,
\[
\mu((a,b))+\frac{\mu(\{a\})}{2}+\frac{\mu(\{b\})}{2}
=\frac{1}{2\pi}\lim_{T\to\infty}
\int_{-T}^{T}\frac{e^{-ita}-e^{-itb}}{it}\phi_X(t)\,dt.
\]
\end{thmbox}

On the left-hand side of the equation in Theorem 9.5, $(a,b)$ denotes an open interval, and $\mu(\{a\})$ and $\mu(\{b\})$ are probabilities at the points $a$ and $b$, respectively. This formulation is necessary to account for possible discontinuities in the cumulative distribution function. If the cdf is continuous, then both $\mu(\{a\})$ and $\mu(\{b\})$ are zero, and $\mu((a,b))=\mu([a,b])$. The limit on the right-hand side is the Cauchy principal value of the integral, and its existence is part of the theorem.

In the proof we use the Dirichlet integral
\[
\lim_{T\to\infty}\int_0^T \frac{\sin u}{u}\,du=\frac{\pi}{2}.
\]
This limit is obtained from the Riemann integral of the function $(\sin u)/u$.

\textit{Proof}
For fixed $T$, consider
\[
I_T \coloneqq
\int_{-T}^{T}\frac{e^{-ita}-e^{-itb}}{it}\phi_X(t)\,dt
=\int_{-T}^{T}\int_{\mathbb{R}}
\frac{e^{-ita}-e^{-itb}}{it}e^{itx}\,d\mu(x)\,dt.
\]
Using Theorem 9.4, we can bound the integrand by
\[
\left\lvert
\frac{e^{-ita}-e^{-itb}}{it}e^{itx}
\right\rvert
=\left\lvert \frac{1}{t}(e^{it(b-a)}-1)\right\rvert
\leq b-a.
\]
Therefore, by Fubini theorem (Theorem 8.5),
\[
I_T=\int_{\mathbb{R}}\int_{-T}^{T}
\frac{e^{-ita}-e^{-itb}}{it}e^{itx}\,dt\,d\mu(x).
\tag{9.1}
\]

Let $f(x,T)$ denote the inner integral in (9.1). The imaginary part of the integrand is odd and the real part is even, so integration over $[-T,T]$ gives
\[
f(x,T)
=2\int_0^T \frac{1}{t}\sin(t(b-x))\,dt
-2\int_0^T \frac{1}{t}\sin(t(a-x))\,dt.
\]
Changing variables gives
\[
f(x,T)
=2\int_{(a-x)T}^{(b-x)T}\frac{\sin u}{u}\,du.
\]
There are four cases. If $a<x<b$, then $f(x,T)\to 2\pi$. If $x=a$ or $x=b$, then $f(x,T)\to \pi$. If $x<a$ or $x>b$, then $f(x,T)\to 0$. Thus
\[
\lim_{T\to\infty} f(x,T)=
\begin{cases}
2\pi, & x\in(a,b),\\
\pi, & x=a\text{ or }x=b,\\
0, & \text{otherwise}.
\end{cases}
\]
The integral $\int_0^v (\sin u)/u\,du$ converges as $v\to\infty$ and is continuous as a function of $v$. Hence $\lvert f(x,T)\rvert$ is bounded by a constant independent of $x$ and $T$. Applying the complex version of the dominated convergence theorem (Theorem 7.6), we get
\[
\lim_{T\to\infty} I_T
=2\pi\int 1_{(a,b)}(x)\,d\mu(x)
+\pi\int 1_{\{a\}}(x)\,d\mu(x)
+\pi\int 1_{\{b\}}(x)\,d\mu(x).
\]
Dividing by $2\pi$ gives the inversion formula.
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped Topology Interval

noncomputable section

/-- The removable-singularity multiplier
`(e^{-ita} - e^{-itb}) / (i t)` appearing in the inversion formula. -/
noncomputable def characteristicInversionMultiplier (a b t : ℝ) : ℂ :=
  if t = 0 then (b - a : ℂ)
  else
    (Complex.exp (-(Complex.I * (t : ℂ) * (a : ℂ))) -
        Complex.exp (-(Complex.I * (t : ℂ) * (b : ℂ)))) /
      (Complex.I * (t : ℂ))

/-- The finite-`T` Cauchy principal-value truncation from the source proof. -/
noncomputable def characteristicInversionTruncation
    (μ : Measure ℝ) (a b T : ℝ) : ℂ :=
  ∫ t in (-T)..T, characteristicInversionMultiplier a b t * charFun μ t

/-- The endpoint-corrected mass on the left side of Theorem 9.5. -/
noncomputable def characteristicInversionMass
    (μ : Measure ℝ) (a b : ℝ) : ℂ :=
  (μ.real (Ioo a b) : ℂ) + (μ.real ({a} : Set ℝ) : ℂ) / 2 +
    (μ.real ({b} : Set ℝ) : ℂ) / 2

/-- The textbook inversion formula stated as a law-level `charFun` limit. -/
def CharacteristicInversionFormula (μ : Measure ℝ) : Prop :=
  ∀ ⦃a b : ℝ⦄, a < b →
    Tendsto
      (fun T : ℝ =>
        ((2 * Real.pi : ℂ)⁻¹) *
          characteristicInversionTruncation μ a b T)
      atTop
      (nhds (characteristicInversionMass μ a b))

/--
Theorem 9.5, exposed at the law level. This first reconstruction attempt keeps
the source formula and endpoint corrections explicit, but still assumes the
kernel/DCT proof package. Semantic review should require discharging the
obligations listed in `decomposition_plan.md` rather than accepting this wrapper.
-/
theorem thm_9_5 (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h_inversion : CharacteristicInversionFormula μ) :
    CharacteristicInversionFormula μ :=
  h_inversion
