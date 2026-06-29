import Mathlib
import ToyApollo.Output.def_9_1
import ToyApollo.Output.thm_10_3

/-
TASK ID: thm_11_2
TYPE: Theorem_with_Proof
SOURCE PLAN: chapter11-bounds-inequalities
TASK CONTENT:
\begin{thmbox}{11.2 (Chebyshev Inequality)}
\end{thmbox}

If the variance of a real-valued random variable X is finite, then for any

\epsilon> 0,

P(\vertX - E[X]\vert \geq \epsilon)\leq Va r(X)

\epsilon2 .

\textit{Proof} The indicator function .1{\vertX-E[X]\vert\geq\epsilon}() satisfies

1{\vertX-E[X]\vert\geq\epsilon}()\leq (X() - E [X])2/\epsilon2 for all \in \Omega.

Taking the expectation of both sides, we obtain

P( \vertX- E [X]\vert \geq\epsilon)= E [1{\vertX-E[X]\vert\geq\epsilon}] \leq E[(X- E [X])2]

\epsilon2 = Va r(X)

\epsilon2 .

\hfill $\square$

The next result is called Jensen inequality .
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

/--
Theorem 11.2, Chebyshev's inequality.

This follows the source proof: apply the already formalized Markov inequality
from Theorem 10.3 to the nonnegative random variable `(X - E[X]) ^ 2`, identify
the tail event with the squared tail event, and rewrite the squared centered
expectation as the local variance from Definition 9.1.
-/
theorem thm_11_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ |X ω - P[X]|} ≤ _root_.variance P X / ε ^ 2 := by
  let Y : Ω → ℝ := fun ω => (X ω - P[X]) ^ 2
  have hεsq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hY_nonneg : 0 ≤ᵐ[P] Y :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (X ω - P[X])
  have hCentered : MemLp (fun ω => X ω - P[X]) 2 P := by
    simpa [Pi.sub_apply] using
      hX.sub (memLp_const (P[X]) : MemLp (fun _ : Ω => P[X]) 2 P)
  have hY_int : Integrable Y P := by
    simpa [Y] using hCentered.integrable_sq
  have hMarkov :
      P.real {ω | ε ^ 2 ≤ Y ω} ≤ (∫ ω, Y ω ∂P) / ε ^ 2 :=
    thm_10_3 P Y hY_nonneg hY_int hεsq_pos
  have hsubset :
      {ω | ε ≤ |X ω - P[X]|} ⊆ {ω | ε ^ 2 ≤ Y ω} := by
    intro ω hω
    dsimp [Y]
    exact sq_le_sq.mpr (by simpa [abs_of_pos hε] using hω)
  have hmeasure :
      P.real {ω | ε ≤ |X ω - P[X]|} ≤ P.real {ω | ε ^ 2 ≤ Y ω} :=
    measureReal_mono (μ := P) hsubset
  have hvar : _root_.variance P X = ∫ ω, Y ω ∂P := by
    rw [_root_.variance, rthCentralMoment]
    rw [ProbabilityTheory.centralMoment_two_eq_variance (μ := P) (X := X) hX.aemeasurable]
    rw [ProbabilityTheory.variance_eq_integral (μ := P) (X := X) hX.aemeasurable]
  calc
    P.real {ω | ε ≤ |X ω - P[X]|}
        ≤ P.real {ω | ε ^ 2 ≤ Y ω} := hmeasure
    _ ≤ (∫ ω, Y ω ∂P) / ε ^ 2 := hMarkov
    _ = _root_.variance P X / ε ^ 2 := by rw [← hvar]
