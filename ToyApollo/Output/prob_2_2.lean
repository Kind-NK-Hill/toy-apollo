import ToyApollo.Output.def_2_5
import ToyApollo.Output.thm_2_4
import ToyApollo.Output.thm_2_5

open MeasureTheory Set

/-
\textbf{2.2.}
\begin{enumerate}[label=(\alph*)]
    \item Let $A_1,A_2,A_3,\dots$ be a sequence of measurable sets with measure 0 in a measure space. Show that the union $\cup_{i=1}^{\infty} A_i$ has measure 0.
    \item Prove that if $B_1,B_2,B_3,\dots$ is a sequence of events with probability 1 in a probability space, then the intersection $\cap_{i=1}^{\infty} B_i$ has probability 1.
\end{enumerate}
-/
theorem prob_2_2 {α : Type} [MeasurableSpace α] :
    (∀ (μ : Measure α) (A : ℕ → Set α), (∀ i, MeasurableSet (A i)) → (∀ i, μ (A i) = 0) → μ (⋃ i, A i) = 0) ∧
    (∀ (μ : Measure α) [IsProbabilityMeasure μ] (B : ℕ → Set α), (∀ i, MeasurableSet (B i)) → (∀ i, μ (B i) = 1) → μ (⋂ i, B i) = 1) := by
      constructor;
      · aesop;
      · intro μ hμ B hB hB';
        rw [ MeasureTheory.measure_congr, MeasureTheory.IsProbabilityMeasure.measure_univ ];
        simp_all +decide [ Set.compl_iInter ]