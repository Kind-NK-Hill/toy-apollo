import Mathlib

/-
TASK ID: def_13_6
TYPE: Definition
SOURCE PLAN: chapter13-martingale-stopping-time
TASK CONTENT:
\begin{defbox}{13.6}
\end{defbox}

A filtration is a sequence of increasing \sigma-subfields in \mathcal{F}, denoted as .(\mathcal{F}n)\infty

n=0,

such that

\mathcal{F}0 \subseteq \mathcal{F}1 \subseteq \mathcal{F}2 \subseteq\cdot\cdot\cdot .

A sequence of random variables .(Xn)\infty

n=0 is said to be adapted to filtration

(\mathcal{F}n)\infty

n=0 if. Xn is\mathcal{F}n-measurable for all n.

Another way to describe a filtration is to regard the index n as representing

discrete time. At each time n, the filtration captures the information available up

to that point in time. Typically, the first \sigma-field \mathcal{F}0 in the filtration is the trivial

\sigma-field.{\emptyset,\Omega }, ie., at time n = 0, only the trivial events \emptyset and. \Omega are measurable.

The defining property of a filtration is that if something is measurable at time n,

then it continues to be measurable at any future time n' >n As time advances, we

have more available information, and the \sigma-algebras in the filtration become larger.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory

noncomputable section

/-- A filtration is an increasing sequence of sub-sigma-fields of the ambient
sigma-field. -/
def def_13_6_isFiltration {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (𝓕n : ℕ → MeasurableSpace Ω) : Prop :=
  (∀ n : ℕ, 𝓕n n ≤ 𝓕) ∧
    ∀ n m : ℕ, n ≤ m → 𝓕n n ≤ 𝓕n m

/-- A sequence of random variables is adapted to a filtration when `X_n` is
measurable with respect to the information available at time `n`. -/
def def_13_6_adapted {Ω S : Type*} [MeasurableSpace S]
    (𝓕n : ℕ → MeasurableSpace Ω) (X : ℕ → Ω → S) : Prop :=
  ∀ n : ℕ, @Measurable Ω S (𝓕n n) _ (X n)

/-- The trivial initial sigma-field `{∅, Ω}`. -/
@[reducible]
def def_13_6_trivialSigmaField (Ω : Type*) : MeasurableSpace Ω :=
  ⊥

/-- A common convention: the filtration starts with the trivial sigma-field. -/
def def_13_6_startsTrivial {Ω : Type*}
    (𝓕n : ℕ → MeasurableSpace Ω) : Prop :=
  𝓕n 0 = def_13_6_trivialSigmaField Ω

theorem def_13_6_mono {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {𝓕n : ℕ → MeasurableSpace Ω} (h : def_13_6_isFiltration 𝓕n)
    {n m : ℕ} (hnm : n ≤ m) :
    𝓕n n ≤ 𝓕n m :=
  h.2 n m hnm

theorem def_13_6_sub_ambient {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    {𝓕n : ℕ → MeasurableSpace Ω} (h : def_13_6_isFiltration 𝓕n)
    (n : ℕ) :
    𝓕n n ≤ 𝓕 :=
  h.1 n

/-- Exported Definition 13.6: filtration. -/
def def_13_6 {Ω : Type*} [𝓕 : MeasurableSpace Ω]
    (𝓕n : ℕ → MeasurableSpace Ω) : Prop :=
  def_13_6_isFiltration 𝓕n
