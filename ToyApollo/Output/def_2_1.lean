import Mathlib

/-
TASK ID: def_2_1
TYPE: Definition
SOURCE PLAN: 40_chap2_countable_sets
TASK CONTENT:
\begin{defbox}{2.1}
Two sets are said to have the same size, or cardinality, if there exists a bijection between them. A set is said to be \textit{countable} if it can be mapped bijectively to the set of natural numbers. An infinite set that is not countable is called \textit{uncountable}.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open Set

/-- Two sets have the same cardinality when there is a bijection between their subtype
members. -/
def SameCardinality {α β : Type*} (A : Set α) (B : Set β) : Prop :=
  Nonempty (A ≃ B)

/-- The book's strict Definition 2.1: countable means bijective with the natural numbers. -/
def IsCountableSet {α : Type*} (A : Set α) : Prop :=
  SameCardinality A (Set.univ : Set ℕ)

/-- The convention immediately after Definition 2.1: finite-or-countable sets are at most
countable. -/
def IsAtMostCountableSet {α : Type*} (A : Set α) : Prop :=
  A.Countable

/-- An infinite set which is not countable in the book's strict sense. -/
def IsUncountableSet {α : Type*} (A : Set α) : Prop :=
  A.Infinite ∧ ¬ IsCountableSet A

/-- Exported definition for Definition 2.1. -/
def def_2_1 {α : Type*} (A : Set α) : Prop :=
  IsCountableSet A
