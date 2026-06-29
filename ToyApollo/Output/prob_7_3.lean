import ToyApollo.Output.prob_7_3_proof_support

/-
TASK ID: prob_7_3
TYPE: Problem
SOURCE PLAN: 30_chap7_problems
TASK CONTENT:
\textbf{7.3.} Let $f:[a,b]\to \mathbb{R}$ be a bounded function, $\alpha(x)$ a Stieltjes measure function on $[a,b]$, and $\mu$ the Lebesgue--Stieltjes measure induced by $\alpha(x)$. Assume $\mu(\{a\})=0$. Prove the following:
\begin{enumerate}[label=(\alph*)]
    \item $f$ is Riemann--Stieltjes integrable on $[a,b]$ if and only if $f$ is continuous $\mu$-almost everywhere.
    \item If $f$ is Riemann--Stieltjes integrable, then $f$ is integrable with respect to the completion $\bar{\mu}$ of $\mu$, and $\int_a^b f\, d\alpha = \int_{[a,b]} f\, d\bar{\mu}$.
\end{enumerate}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set Filter

noncomputable section

/-- Problem 7.3: Riemann--Stieltjes integrability is equivalent to
almost-everywhere continuity, and the integral agrees with the completed
Lebesgue--Stieltjes integral. -/
theorem prob_7_3
    {a b : ℝ} {f : ℝ → ℝ} {α : StieltjesFunction ℝ}
    (hab : a < b)
    (hBounded : ∃ M, ∀ x ∈ Icc a b, |f x| ≤ M)
    (hAtom : α.measure {a} = 0) :
    (RSIntegrable f α a b ↔
      ∀ᵐ x ∂(α.measure.restrict (Icc a b)), ContinuousWithinAt f (Icc a b) x) ∧
    (∀ hRS : RSIntegrable f α a b,
      IntegrableOn (fun x : NullMeasurableSpace ℝ α.measure => f x) (Icc a b)
          α.measure.completion ∧
        rsIntegral f α a b hRS =
          ∫ x in Icc a b, (fun x : NullMeasurableSpace ℝ α.measure => f x) x
            ∂α.measure.completion) := by
  simpa using prob_7_3_support_result
    (a := a) (b := b) (f := f) (α := α) hab hBounded hAtom
