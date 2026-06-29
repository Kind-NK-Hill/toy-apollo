import Mathlib
import ToyApollo.Output.thm_10_1
import ToyApollo.Output.thm_10_3
import ToyApollo.Output.thm_5_8

/-
TASK ID: thm_10_4
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter10-almost-sure-probability
TASK CONTENT:
\begin{thmbox}{10.4}
Suppose $(X_n)_{n=1}^{\infty}$ is a sequence of nonnegative random variables. If
\[
\sum_{n=1}^{\infty}\mathbb{E}[X_n]<\infty,
\]
then the sequence $(X_n)_{n=1}^{\infty}$ converges to $0$ almost surely.
\end{thmbox}

\textit{Proof}
Fix a positive real number $\epsilon$. By Markov inequality, we have
\[
\sum_{n=1}^{\infty}P(X_n>\epsilon)
\leq
\sum_{n=1}^{\infty}\frac{\mathbb{E}[X_n]}{\epsilon}.
\]
Since $\sum_{n=1}^{\infty}\mathbb{E}[X_n]$ is finite, the summation on the left-hand side is also finite. By the Borel--Cantelli lemma (Theorem 5.8), we have $P(X_n>\epsilon\ \mathrm{i.o.})=0$. Since this holds for all $\epsilon>0$, we can apply Theorem 10.1 and conclude that $X_n\xrightarrow{\mathrm{a.s.}}0$. Note that we need not assume independence in this proof.
\hfill $\square$
-/

-- WRITE FINAL LEAN CODE BELOW

open Filter MeasureTheory Set
open scoped ENNReal Topology BigOperators

/--
Theorem 10.4: summability of the first absolute moments implies almost-sure
convergence to zero.  For the textbook's nonnegative random variables,
`|Xn n|` is just `Xn n`; the absolute-value formulation avoids adding a
separate nonnegativity transport lemma.
-/
theorem thm_10_4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Xn : ℕ → Ω → ℝ)
    (h_aemeas : ∀ n : ℕ,
      AEMeasurable (fun ω : Ω => ENNReal.ofReal |Xn n ω|) μ)
    (h_moment_summable :
      (∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal |Xn n ω| ∂μ) ≠ ∞) :
    ConvergesAlmostSurely μ Xn (fun _ => 0) := by
  refine (thm_10_1 μ Xn (fun _ => 0)).2 ?_
  intro ε hε
  have hε_ne_zero : ENNReal.ofReal ε ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hε)
  have hε_ne_top : ENNReal.ofReal ε ≠ ∞ := ENNReal.ofReal_ne_top
  have hterm :
      ∀ n : ℕ,
        μ (almostSureDeviationEvent Xn (fun _ => 0) n ε) ≤
          (∫⁻ ω, ENNReal.ofReal |Xn n ω| ∂μ) / ENNReal.ofReal ε := by
    intro n
    have hsubset :
        almostSureDeviationEvent Xn (fun _ => 0) n ε ⊆
          {ω : Ω | ENNReal.ofReal ε ≤ ENNReal.ofReal |Xn n ω|} := by
      intro ω hω
      have hreal : ε ≤ |Xn n ω| := by
        have hstrict : ε < |Xn n ω - 0| := by
          simpa [almostSureDeviationEvent] using hω
        simpa using le_of_lt hstrict
      exact ENNReal.ofReal_le_ofReal hreal
    exact (measure_mono hsubset).trans
      (meas_ge_le_lintegral_div (h_aemeas n) hε_ne_zero hε_ne_top)
  have hdeviation_summable :
      (∑' n : ℕ, μ (almostSureDeviationEvent Xn (fun _ => 0) n ε)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    have hsum_div :
        (∑' n : ℕ, (∫⁻ ω, ENNReal.ofReal |Xn n ω| ∂μ) / ENNReal.ofReal ε) =
          (∑' n : ℕ, ∫⁻ ω, ENNReal.ofReal |Xn n ω| ∂μ) / ENNReal.ofReal ε := by
      simp [div_eq_mul_inv, ENNReal.tsum_mul_right]
    rw [hsum_div]
    exact ENNReal.div_ne_top h_moment_summable hε_ne_zero
  exact thm_5_8 μ (fun n : ℕ => almostSureDeviationEvent Xn (fun _ => 0) n ε)
    hdeviation_summable
