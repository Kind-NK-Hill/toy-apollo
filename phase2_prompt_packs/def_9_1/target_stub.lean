import Mathlib

/-
TASK ID: def_9_1
TYPE: Definition
SOURCE PLAN: chapter9-moments-mgf
TASK CONTENT:
\begin{defbox}{9.1}
For an integer $r \geq 1$, the $r$-th moment of $X$ is defined as the expectation $\mathbb{E}[X^r]$. The $r$-th central moment is defined by $\mathbb{E}[(X-\mathbb{E}[X])^r]$. In particular, the second central moment is commonly called the variance of $X$; the square root of variance is called the standard deviation.

The third central moment measures the asymmetry of the probability distribution. The skewness of a random variable is defined as the third central moment normalized by the cube of the standard deviation $\sigma$,
\[
\frac{\mathbb{E}[(X-\mathbb{E}[X])^3]}{\sigma^3}.
\]
The analogous quantity of order $4$ is called the kurtosis,
\[
\frac{\mathbb{E}[(X-\mathbb{E}[X])^4]}{\sigma^4}.
\]
It measures the tailedness of the probability distribution.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW
