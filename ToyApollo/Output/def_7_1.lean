import Mathlib

/-
TASK ID: def_7_1
TYPE: Definition
SOURCE PLAN: 25_chap7_ae_equality
TASK CONTENT:
\begin{defbox}{7.1}
Consider two integrable functions $f$ and $g$ defined on the same measure space $(\Omega,\mathcal{F},\mu)$. We say that $f$ and $g$ are \textit{equal everywhere} if $f(\omega)=g(\omega)$ for all $\omega \in \Omega$. We say that $f$ and $g$ are \textit{equal almost everywhere} if there exists an $\mathcal{F}$-measurable set $A$ with $\mu(A)=0$ such that $f(\omega)=g(\omega)$ for all $\omega$ in $A^c$. We say that two integrable functions are \textit{equivalent} if they are equal almost everywhere. When the measure space is a probability space, we also say that random variables $X$ and $Y$ are equal, \textit{almost surely}, or \textit{with probability 1}, simply a.e., a.s., or w.p.1, if they are equal almost everywhere.
\end{defbox}
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory Set

/-- Textbook notion: `f` and `g` are equal everywhere on `Ω`. -/
def EqualEverywhere {Ω E : Type*} (f g : Ω → E) : Prop :=
  ∀ ω, f ω = g ω

/-- Textbook notion: `f` and `g` are equal almost everywhere with respect to `μ`. -/
def EqualAlmostEverywhere {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → E) : Prop :=
  ∃ A : Set Ω, MeasurableSet A ∧ μ A = 0 ∧ EqOn f g Aᶜ

/-- Textbook notion: equivalence modulo a null set. -/
def EquivalentFunctions {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → E) : Prop :=
  EqualAlmostEverywhere μ f g

/-- Exported definition for Definition 7.1. -/
def def_7_1 {Ω E : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → E) :
    Prop :=
  EquivalentFunctions μ f g
