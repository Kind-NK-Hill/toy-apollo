import ToyApollo.Output.def_2_5
import ToyApollo.Output.thm_2_3
import ToyApollo.Output.thm_2_4

open MeasureTheory Set Finset

/--
PROBLEM
\textbf{2.4.} (Union bound) For any $n$ events $A_1,A_2,\dots,A_n$, prove that
\[
\Pr(A_1\cup A_2\cup \cdots \cup A_n)\le \sum_{i=1}^{n} \Pr(A_i).
\]

Use the property of continuity from below to prove that, for any sequence of $\mathcal{F}$-measurable sets $A_n$, for $n\ge 1$, we have
\[
\Pr\left(\bigcup_{i=1}^{\infty} A_i\right)\le \sum_{i=1}^{\infty} \Pr(A_i).
\]

HARD DEPENDENCIES (plan-derived and mandatory imports already uploaded as local Lean files)
- (none)

SOFT IMPORTS (externally selected but mandatory imports already uploaded as local Lean files)
- def_2_5 | type=Definition | title=Definition 2.5 (Measure) | source_plan=42_chap2_measure_functions
  latex=\begin{defbox}{2.5} Let $\mathcal{F}$ be a $\sigma$-field on a sample space $\Omega$. A set function $m$ from $\mathcal{F}$ to $[0,\infty]$ is called a \textit{measure} if it satisfies the following properties: \begin{enumerate}[label=\arabic*.] \item $m(\emptyset)=0$. \item For any sequence of mutually disjoint $A_i\in \mathcal{F}$, for $i=1,2,3,\dots$, we have \[ m\left(\biguplus_{i=1}^{\infty} A_i\right) = \sum_{i=1}^{\infty} m(A_i). \] \end{enumerate} This property is known as the $\sigma$-\textit{additive} property. A measure $m$ is said to be \textit{finite} if $m(\Omega)$ is finite. If $m(\Omega)=1$, then $m$ is called a \textit{probability measure}. A \textit{measure space} is a triple $(\Omega,\mathcal{F},m)$ where $\mathcal{F}$ is a $\sigma$-field on $\Omega$ and $m$ is a meas...
- thm_2_3 | type=Theorem_with_Proof | title=Theorem 2.3 (Finite Subadditivity) | source_plan=42_chap2_measure_functions
  latex=\begin{thmbox}{2.3 (Finite Subadditivity)} Let $(\Omega,\mathcal{F},\mu)$ be a measure space, and suppose $A$ and $B$ are $\mathcal{F}$-measurable sets. Then \[ \mu(A\cup B)\le \mu(A)+\mu(B). \] \end{thmbox} \textit{Proof} $\mu(A\cup B)=\mu(A \uplus (B\setminus A))=\mu(A)+\mu(B\setminus A)\le \mu(A)+\mu(B)$. \hfill $\square$ The next general property is about an increasing and decreasing sequence of events.
- thm_2_4 | type=Theorem_with_Proof | title=Theorem 2.4 (Lower Semi-Continuity) | source_plan=42_chap2_measure_functions
  latex=\begin{thmbox}{2.4 (Lower Semi-Continuity)} Suppose $A_1\subseteq A_2\subseteq A_3\subseteq \cdots$ is a sequence of increasing sets in $\mathcal{F}$ and $(\Omega,\mathcal{F},\mu)$ is a measure space. Then \[ \lim_{k\to\infty} \mu(A_k)=\mu\left(\bigcup_{i=1}^{\infty} A_i\right). \] \end{thmbox} \textit{Proof} Let $B_1=A_1$ and $B_i=A_i\setminus A_{i-1}$ for $i\ge 2$. The sets $B_i$'s are mutually disjoint by construction. Moreover, we have $\biguplus_{i=1}^{\infty} B_i=\cup_{i=1}^{\infty} A_i$. This gives \[ \lim_{k\to\infty} \mu(A_k) = \lim_{k\to\infty} \mu(B_1 \uplus B_2 \uplus \cdots \uplus B_k) \] \[ = \lim_{k\to\infty} \sum_{i=1}^{k} \mu(B_i) \triangleq \sum_{i=1}^{\infty} \mu(B_i) = \mu\left(\biguplus_{i=1}^{\infty} B_i\right) = \mu\left(\bigcup_{i=1}^{\infty} A_i\right), \] where...

FINAL IMPORT UNION (all listed files are mandatory imports and physically included in this package)
- def_2_5 | type=Definition | title=Definition 2.5 (Measure) | source_plan=42_chap2_measure_functions
  latex=\begin{defbox}{2.5} Let $\mathcal{F}$ be a $\sigma$-field on a sample space $\Omega$. A set function $m$ from $\mathcal{F}$ to $[0,\infty]$ is called a \textit{measure} if it satisfies the following properties: \begin{enumerate}[label=\arabic*.] \item $m(\emptyset)=0$. \item For any sequence of mutually disjoint $A_i\in \mathcal{F}$, for $i=1,2,3,\dots$, we have \[ m\left(\biguplus_{i=1}^{\infty} A_i\right) = \sum_{i=1}^{\infty} m(A_i). \] \end{enumerate} This property is known as the $\sigma$-\textit{additive} property. A measure $m$ is said to be \textit{finite} if $m(\Omega)$ is finite. If $m(\Omega)=1$, then $m$ is called a \textit{probability measure}. A \textit{measure space} is a triple $(\Omega,\mathcal{F},m)$ where $\mathcal{F}$ is a $\sigma$-field on $\Omega$ and $m$ is a meas...
- thm_2_3 | type=Theorem_with_Proof | title=Theorem 2.3 (Finite Subadditivity) | source_plan=42_chap2_measure_functions
  latex=\begin{thmbox}{2.3 (Finite Subadditivity)} Let $(\Omega,\mathcal{F},\mu)$ be a measure space, and suppose $A$ and $B$ are $\mathcal{F}$-measurable sets. Then \[ \mu(A\cup B)\le \mu(A)+\mu(B). \] \end{thmbox} \textit{Proof} $\mu(A\cup B)=\mu(A \uplus (B\setminus A))=\mu(A)+\mu(B\setminus A)\le \mu(A)+\mu(B)$. \hfill $\square$ The next general property is about an increasing and decreasing sequence of events.
- thm_2_4 | type=Theorem_with_Proof | title=Theorem 2.4 (Lower Semi-Continuity) | source_plan=42_chap2_measure_functions
  latex=\begin{thmbox}{2.4 (Lower Semi-Continuity)} Suppose $A_1\subseteq A_2\subseteq A_3\subseteq \cdots$ is a sequence of increasing sets in $\mathcal{F}$ and $(\Omega,\mathcal{F},\mu)$ is a measure space. Then \[ \lim_{k\to\infty} \mu(A_k)=\mu\left(\bigcup_{i=1}^{\infty} A_i\right). \] \end{thmbox} \textit{Proof} Let $B_1=A_1$ and $B_i=A_i\setminus A_{i-1}$ for $i\ge 2$. The sets $B_i$'s are mutually disjoint by construction. Moreover, we have $\biguplus_{i=1}^{\infty} B_i=\cup_{i=1}^{\infty} A_i$. This gives \[ \lim_{k\to\infty} \mu(A_k) = \lim_{k\to\infty} \mu(B_1 \uplus B_2 \uplus \cdots \uplus B_k) \] \[ = \lim_{k\to\infty} \sum_{i=1}^{k} \mu(B_i) \triangleq \sum_{i=1}^{\infty} \mu(B_i) = \mu\left(\biguplus_{i=1}^{\infty} B_i\right) = \mu\left(\bigcup_{i=1}^{\infty} A_i\right), \] where...

PROVIDED SOLUTION
This is a whole-task formalization. 
Please construct the Lean 4 proof.
The hard dependencies and soft imports above are all mandatory imports once selected.
The imported local dependencies above are physically present in ToyApollo/Output and must be reused when applicable.
Do not redefine concepts or theorems that are already provided by imported local dependencies.
For chapter-local limsup/liminf sequence problems, prefer the textbook semantics already provided by imported local dependencies such as `seqLimsup` / `seqLiminf` instead of defaulting to `Filter.limsup` on `ℝ`.
-/
theorem prob_2_4_finset_union_bound {α : Type _} [MeasurableSpace α]
    (μ : Measure α) {ι : Type _} (s : Finset ι) (A : ι → Set α) :
    μ (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ (A i) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro a s has ih
    have hunion : (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by
      ext x
      simp
    calc
      μ (⋃ i ∈ insert a s, A i) = μ (A a ∪ ⋃ i ∈ s, A i) := by rw [hunion]
      _ ≤ μ (A a) + μ (⋃ i ∈ s, A i) := thm_2_3 μ (A a) (⋃ i ∈ s, A i)
      _ ≤ μ (A a) + ∑ i ∈ s, μ (A i) := add_le_add le_rfl ih
      _ = ∑ i ∈ insert a s, μ (A i) := by
        simp [has]

theorem prob_2_4 {α : Type _} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    (∀ (n : ℕ) (A : Fin n → Set α), (∀ i, MeasurableSet (A i)) → μ (⋃ i, A i) ≤ ∑ i, μ (A i)) ∧
    (∀ (A : ℕ → Set α), (∀ i, MeasurableSet (A i)) → μ (⋃ i, A i) ≤ ∑' i, μ (A i)) := by
  refine ⟨?finite, ?countable⟩
  · intro n A _hA
    simpa using
      (prob_2_4_finset_union_bound μ (Finset.univ : Finset (Fin n)) A)
  · intro A hAmeas
    let U : ℕ → Set α := fun n => ⋃ i ∈ Finset.range (n + 1), A i
    have hUinc : SetSeqIncreasing U := by
      change Monotone U
      intro m n hmn
      intro x hx
      rcases mem_iUnion.mp hx with ⟨i, hi⟩
      rcases mem_iUnion.mp hi with ⟨hi_range, hxi⟩
      refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨?_, hxi⟩⟩
      exact Finset.mem_range.mpr (by
        have hi : i < m + 1 := Finset.mem_range.mp hi_range
        omega)
    have hUmeas : ∀ n, MeasurableSet (U n) := by
      intro n
      exact Finset.measurableSet_biUnion (Finset.range (n + 1)) (fun i _hi => hAmeas i)
    have hUnion : (⋃ n, U n) = ⋃ i, A i := by
      ext x
      constructor
      · intro hx
        rcases mem_iUnion.mp hx with ⟨n, hn⟩
        rcases mem_iUnion.mp hn with ⟨i, hi⟩
        rcases mem_iUnion.mp hi with ⟨_hi_range, hxi⟩
        exact mem_iUnion.mpr ⟨i, hxi⟩
      · intro hx
        rcases mem_iUnion.mp hx with ⟨i, hxi⟩
        refine mem_iUnion.mpr ⟨i, ?_⟩
        refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨?_, hxi⟩⟩
        simp
    have hfinite_bound :
        ∀ n, μ (U n) ≤ ∑ i ∈ Finset.range (n + 1), μ (A i) := by
      intro n
      exact prob_2_4_finset_union_bound μ (Finset.range (n + 1)) A
    have hpartial_le_tsum : ∀ n, μ (U n) ≤ ∑' i, μ (A i) := by
      intro n
      exact (hfinite_bound n).trans (ENNReal.sum_le_tsum (Finset.range (n + 1)))
    calc
      μ (⋃ i, A i) = μ (⋃ n, U n) := by rw [hUnion]
      _ = ⨆ n, μ (U n) := thm_2_4 μ U hUinc hUmeas
      _ ≤ ∑' i, μ (A i) := iSup_le hpartial_le_tsum
