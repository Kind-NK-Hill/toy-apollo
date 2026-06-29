import Mathlib
import ToyApollo.Output.def_4_1
import ToyApollo.Output.thm_6_7__lemma_1

/-
TASK ID: thm_11_3
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-bounds-inequalities
TASK CONTENT:
\begin{thmbox}{11.3 (Jensen Inequality)}
\end{thmbox}

Suppose \phi is a convex function and X is a real-valued random variable with

finite mean. Then E[\phi(X)]\geq \phi(E[X]).

\textit{Proof} By the convexity of \phi, at each point x* in the domain of \phi, we can draw a

straight line that touches the graph of \phi at one point, ie., it passes through the point

(x*,\phi( x*)) and lies beneath the graph of \phi(x).

We pick x* =E [X], which is finite by assumption. Let g(x)= ax + b be a

linear function such that g(E[X])= \phi(E [X]) andg(x)\leq \phi(x) for all x I f \phi is not

differentiable at x* =E [X], there could be more than one choice of coefficients a

and b In this case, we just pick one arbitrarily.

By applying the monotonic property of integral, we obtain

E[\phi(X)]\geq E[g(X)]= aE[X]+ bE[1]= aE[X]+ b= \phi(E [X]).

Note that we have used E[1]= 1 in the second last equality. \hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory

/--
Theorem 11.3, Jensen's inequality.

The textbook proof draws a supporting line to the convex graph at `E[X]` and
then integrates the pointwise lower bound.  The formal statement uses the
whole-real-line domain from the source and exposes two analytic well-formedness
conditions needed by the integral Jensen theorem: continuity of `phi` and
integrability of `phi o X`.
-/
theorem thm_11_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {φ : ℝ → ℝ} {X : Ω → ℝ}
    (hXrv : IsRealMeasurable X) (hφ : ConvexOn ℝ Set.univ φ)
    (hφc : ContinuousOn φ Set.univ) (hX : Integrable X P)
    (hφX : Integrable (φ ∘ X) P) :
    φ (P[X]) ≤ P[fun ω => φ (X ω)] := by
  have _ : Measurable X := hXrv
  have hXmem : ∀ᵐ ω ∂P, X ω ∈ (Set.univ : Set ℝ) := by simp
  exact ConvexOn.map_integral_le hφ hφc isClosed_univ hXmem hX hφX

/--
The same Jensen inequality together with the local Chapter 6 bridge identifying
the textbook expectation definition with the integral notation used in the
formal inequality.
-/
theorem thm_11_3_textbook_expectation_bridge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {φ : ℝ → ℝ} {X : Ω → ℝ}
    (hXrv : IsRealMeasurable X) (hφX_meas : Measurable (fun ω => φ (X ω)))
    (hφ : ConvexOn ℝ Set.univ φ) (hφc : ContinuousOn φ Set.univ) (hX : Integrable X P)
    (hφX : Integrable (φ ∘ X) P) :
    expectation P (fun ω => (X ω : EReal)) = some (Real.toEReal (P[X])) ∧
      expectation P (fun ω => (φ (X ω) : EReal)) =
        some (Real.toEReal (P[fun ω => φ (X ω)])) ∧
      φ (P[X]) ≤ P[fun ω => φ (X ω)] := by
  have hX_meas : Measurable X := hXrv
  refine ⟨?_, ?_, ?_⟩
  · exact chapter6_expectation_real_eq_integral (P := P) (f := X) hX_meas hX
  · exact chapter6_expectation_real_eq_integral (P := P) (f := fun ω => φ (X ω))
      hφX_meas hφX
  · exact thm_11_3 P hXrv hφ hφc hX hφX
