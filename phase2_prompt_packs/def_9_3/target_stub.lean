import Mathlib
import ToyApollo.Output.def_6_6

/-
TASK ID: def_9_3
TYPE: Definition
SOURCE PLAN: chapter9-characteristic-functions
TASK CONTENT:
\begin{defbox}{9.3}
Given a real-valued random variable $X$, define the characteristic function of $X$ by
\[
\phi_X(t) \coloneqq \mathbb{E}[e^{iXt}]
= \int_{\Omega} e^{iX(\omega)t}\,dP(\omega)
\]
for $t\in\mathbb{R}$.

If $X$ is a continuous random variable with pdf $f(x)$, we can compute its characteristic function by
\[
\int e^{ixt}f(x)\,dx.
\]
If $X$ is a discrete random variable with pmf $p(n)$, the characteristic function is equal to
\[
\sum_n e^{int}p(n).
\]
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW
