import Mathlib

/-
TASK ID: def_2_2
TYPE: Definition
SOURCE PLAN: 41_chap2_algebra_of_events
TASK CONTENT:
\begin{defbox}{2.2}
A collection of subsets $\mathcal{F}$ of a sample space $\Omega$ is called an \textit{algebra} or a \textit{field} if it satisfies the following axioms:
\begin{enumerate}[label=\arabic*.]
    \item The entire sample space $\Omega$ is an element of the collection: $\Omega\in \mathcal{F}$.
    \item The collection is closed under finite unions: $A\in \mathcal{F}$ and $B\in \mathcal{F}$ imply $A\cup B\in \mathcal{F}$.
    \item The collection is closed under complement: If $A\in \mathcal{F}$, then its complement $A^c$ (taken relative to $\Omega$) is in $\mathcal{F}$.
\end{enumerate}

A set in $\mathcal{F}$ is called an \textit{event}.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open Set

/-- An algebra (field) of events on a sample space. -/
structure EventAlgebra (Ω : Type*) where
  carrier : Set (Set Ω)
  univ_mem : Set.univ ∈ carrier
  union_mem : ∀ {A B : Set Ω}, A ∈ carrier → B ∈ carrier → A ∪ B ∈ carrier
  compl_mem : ∀ {A : Set Ω}, A ∈ carrier → Aᶜ ∈ carrier

/-- Membership in an event algebra. -/
def IsEvent {Ω : Type*} (𝓕 : EventAlgebra Ω) (A : Set Ω) : Prop :=
  A ∈ 𝓕.carrier

/-- Exported definition for Definition 2.2. -/
def def_2_2 (Ω : Type*) : Type _ :=
  EventAlgebra Ω
