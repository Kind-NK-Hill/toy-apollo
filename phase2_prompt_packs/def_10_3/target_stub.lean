import Mathlib


/-
TASK ID: def_10_3
TYPE: Definition
SOURCE PLAN: chapter10-mean
TASK CONTENT:
\begin{defbox}{10.3}
For $r\geq 1$, $(X_n)_{n\geq 1}$ is said to converge to $X$ in the $r$-th mean (or in the $L^r$ norm) if
\[
\mathbb{E}[\lvert X_n-X\rvert^r]\to 0
\]
as $n\to\infty$.

When $r=1$, we say that $X_n$ converges to $X$ in the mean. When $r=2$, we say that $X_n$ converges to $X$ in mean square or in quadratic mean. Other notation for mean square convergence includes
\[
X_n\xrightarrow{\mathrm{m.s.}}X
\qquad\text{and}\qquad
\operatorname{l.i.m.} X_n=X.
\]
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW
