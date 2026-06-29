import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-
TASK ID: ex_6_3_2
TYPE: Example_Proof
SOURCE PLAN: 21_chap6_real_complex_functions
TASK CONTENT:
\textbf{Example 6.3.2 (An Example of Complex Integral)} \\
Take $\Omega=[0,1]$ as the sample space and $\mu$ be the Lebesgue measure on $[0,1]$. Assume for the time being that the integral with respect to the Lebesgue measure can be computed by Riemann integral. (This will be proved in the next chapter.)

Let $t$ be a real number. We are interested in computing the integral
\[
\phi(t)=\int_{\Omega} e^{ixt}\, d\mu(x)
\]
as a function of $t$. By using Euler's formula, we can write $e^{ixt}$ as $\cos(xt)+i\sin(xt)$ and compute the complex integral as
\[
\phi(t)=\int_{\Omega} e^{ixt}\, d\mu(x)
\triangleq \int_{0}^{1} \cos(xt)\, dx + i\int_{0}^{1} \sin(xt)\, dx.
\]

When $t$ is nonzero, it is equal to
\[
\left[\frac{\sin(xt)}{t}\right]_{0}^{1}
+i\left[-\frac{\cos(xt)}{t}\right]_{0}^{1}
=\frac{\sin(t)-i\cos(t)+i}{t}
=\frac{i-ie^{it}}{t}.
\]

The next theorem provides a useful criterion for determining whether a measurable function is integrable.
-/

-- WRITE FINAL LEAN CODE BELOW

open intervalIntegral Complex

/-- The characteristic-function style integral from Example 6.3.2. -/
noncomputable def complexPhi (t : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, Complex.exp (((t : ℂ) * Complex.I) * x)

/-- Example 6.3.2: for `t ≠ 0`, the complex integral over `[0,1]` has the
closed form `(i - i e^{it}) / t`. -/
theorem ex_6_3_2 (t : ℝ) (ht : t ≠ 0) :
    complexPhi t = (Complex.I - Complex.I * Complex.exp ((t : ℂ) * Complex.I)) / (t : ℂ) := by
  have htC : ((t : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  rw [complexPhi, integral_exp_mul_complex htC]
  field_simp [ht]
  ring_nf
  simp [Complex.exp_mul_I]
  ring
