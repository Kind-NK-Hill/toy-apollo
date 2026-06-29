import Mathlib

/-
TASK ID: def_2_6
TYPE: Definition
SOURCE PLAN: 42_chap2_measure_functions
TASK CONTENT:
\begin{defbox}{2.6}
A sequence of sets $A_i$, for $i=1,2,3,\dots$, is said to be \textit{increasing} if $A_1\subseteq A_2\subseteq A_3\subseteq \cdots$, or \textit{decreasing} if $A_1\supseteq A_2\supseteq A_3\supseteq \cdots$.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open Set

/-- A sequence of sets is increasing when each earlier set is contained in each later set. -/
def SetSeqIncreasing {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  Monotone A

/-- A sequence of sets is decreasing when each earlier set contains each later set. -/
def SetSeqDecreasing {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  Antitone A

/-- Exported increasing-sequence half of Definition 2.6. -/
def def_2_6 {Ω : Type*} (A : ℕ → Set Ω) : Prop :=
  SetSeqIncreasing A
