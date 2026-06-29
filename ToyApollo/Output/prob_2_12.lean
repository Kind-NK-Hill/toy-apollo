import ToyApollo.Output.def_2_2

/-
\textbf{2.12.} Suppose $\mathcal{A}$ is a collection of subsets in $\Omega$ such that (a) $\Omega\in \mathcal{A}$, (b) $\mathcal{A}$ is closed under taking set difference, i.e., $A,B\in \mathcal{A}$ implies $B\setminus A\in \mathcal{A}$. Show that $\mathcal{A}$ is a field.

HARD DEPENDENCIES (plan-derived and mandatory imports already uploaded as local Lean files)
- (none)

SOFT IMPORTS (externally selected but mandatory imports already uploaded as local Lean files)
- def_2_2 | type=Definition | title=Definition 2.2 (Algebra / Field of Events) | source_plan=41_chap2_algebra_of_events
  latex=\begin{defbox}{2.2} A collection of subsets $\mathcal{F}$ of a sample space $\Omega$ is called an \textit{algebra} or a \textit{field} if it satisfies the following axioms: \begin{enumerate}[label=\arabic*.] \item The entire sample space $\Omega$ is an element of the collection: $\Omega\in \mathcal{F}$. \item The collection is closed under finite unions: $A\in \mathcal{F}$ and $B\in \mathcal{F}$ imply $A\cup B\in \mathcal{F}$. \item The collection is closed under complement: If $A\in \mathcal{F}$, then its complement $A^c$ (taken relative to $\Omega$) is in $\mathcal{F}$. \end{enumerate} A set in $\mathcal{F}$ is called an \textit{event}. \end{defbox}

FINAL IMPORT UNION (all listed files are mandatory imports and physically included in this package)
- def_2_2 | type=Definition | title=Definition 2.2 (Algebra / Field of Events) | source_plan=41_chap2_algebra_of_events
  latex=\begin{defbox}{2.2} A collection of subsets $\mathcal{F}$ of a sample space $\Omega$ is called an \textit{algebra} or a \textit{field} if it satisfies the following axioms: \begin{enumerate}[label=\arabic*.] \item The entire sample space $\Omega$ is an element of the collection: $\Omega\in \mathcal{F}$. \item The collection is closed under finite unions: $A\in \mathcal{F}$ and $B\in \mathcal{F}$ imply $A\cup B\in \mathcal{F}$. \item The collection is closed under complement: If $A\in \mathcal{F}$, then its complement $A^c$ (taken relative to $\Omega$) is in $\mathcal{F}$. \end{enumerate} A set in $\mathcal{F}$ is called an \textit{event}. \end{defbox}
-/
theorem prob_2_12 (Ω : Type _) (𝒜 : Set (Set Ω)) (h_univ : Set.univ ∈ 𝒜)
    (h_diff : ∀ A B, A ∈ 𝒜 → B ∈ 𝒜 → B \ A ∈ 𝒜) :
    ∅ ∈ 𝒜 ∧ (∀ A, A ∈ 𝒜 → Aᶜ ∈ 𝒜) ∧ (∀ A B, A ∈ 𝒜 → B ∈ 𝒜 → A ∪ B ∈ 𝒜) := by
      have h_empty : ∅ ∈ 𝒜 := by
        simpa using h_diff _ _ h_univ h_univ
      have h_compl : ∀ A ∈ 𝒜, Aᶜ ∈ 𝒜 := by
        exact fun A hA => by simpa [ Set.diff_eq ] using h_diff A Set.univ hA h_univ;
      have h_union : ∀ A B, A ∈ 𝒜 → B ∈ 𝒜 → A ∪ B ∈ 𝒜 := by
        intro A B hA hB;
        convert h_compl _ ( h_diff _ _ hA ( h_compl _ hB ) ) using 1 ; ext ; simp +decide ; tauto;
      exact ⟨h_empty, h_compl, h_union⟩

/-- The collection in Problem 2.12, packaged as an event algebra/field. -/
def prob_2_12_eventAlgebra (Ω : Type _) (𝒜 : Set (Set Ω)) (h_univ : Set.univ ∈ 𝒜)
    (h_diff : ∀ A B, A ∈ 𝒜 → B ∈ 𝒜 → B \ A ∈ 𝒜) : EventAlgebra Ω where
  carrier := 𝒜
  univ_mem := h_univ
  union_mem := by
    intro A B hA hB
    exact (prob_2_12 Ω 𝒜 h_univ h_diff).2.2 A B hA hB
  compl_mem := by
    intro A hA
    exact (prob_2_12 Ω 𝒜 h_univ h_diff).2.1 A hA

/-- Therefore `𝒜` is a field of events in the sense of Definition 2.2. -/
theorem prob_2_12_is_field (Ω : Type _) (𝒜 : Set (Set Ω)) (h_univ : Set.univ ∈ 𝒜)
    (h_diff : ∀ A B, A ∈ 𝒜 → B ∈ 𝒜 → B \ A ∈ 𝒜) :
    ∃ 𝓕 : EventAlgebra Ω, 𝓕.carrier = 𝒜 := by
  exact ⟨prob_2_12_eventAlgebra Ω 𝒜 h_univ h_diff, rfl⟩
