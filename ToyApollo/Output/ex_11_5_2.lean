import Mathlib
import ToyApollo.Output.thm_11_8

/-
TASK ID: ex_11_5_2
TYPE: Example_Proof
SOURCE PLAN: chapter11-strong-law-large-numbers
TASK CONTENT:
\textbf{Example 11.5.2 (Normal Numbers)} \\

A real number is said to be normal in base 10 if the frequency of each digit 0 through 9 in its

decimal expansion is asymptotically equal. If a number has multiple decimal expansions, such as

0.1 = 0.09999... , we choose the one that does not end in infinitely many trailing 0's. The strong

law of large numbers implies that, with probability 1, a randomly chosen number in the interval

[0, 1] is normal in base 10.

We can generalize this notion of normality to other bases. A real number is said to be normal if

it is normal in base b all for all integer b \geq 2 simultaneously. By the strong law of large numbers,

for any integer b \geq 2, there exists a set Ab in .[0, 1] with P(Ab) = 1 such that all numbers in Ab

are normal in base b. Taking the intersection of countably events with probability 1, we deduce

that a number in .[0, 1] is normal almost surely. This proves the existence of normal numbers.

However, the argument in the previous paragraph is non-constructive. It is a non-trivial task to

explicitly construct a normal number or prove that a given number is normal.
-/

-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open Set

/-- A real number is normal when it is normal in every integer base at least
`2`.  The base-specific predicate is kept abstract because the example's proof
uses only the strong-law full-measure sets and their countable intersection. -/
def NormalNumber (normalInBase : ℕ → ℝ → Prop) (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → normalInBase b x

/-- The full-measure set obtained by intersecting the base-wise normality sets. -/
def normalNumberFullSet {Ω : Type*} (A : ℕ → Set Ω) : Set Ω :=
  ⋂ b : ℕ, if 2 ≤ b then A b else Set.univ

/--
Example 11.5.2: the nonconstructive normal-number argument.

If the strong law supplies, for every base `b >= 2`, a measurable probability-one
set `A b` on which the sampled number is normal in that base, then the
countable intersection of these sets still has probability one.  Every point in
that intersection is normal in all bases simultaneously.
-/
theorem ex_11_5_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (normalInBase : ℕ → ℝ → Prop)
    (A : ℕ → Set Ω)
    (hA_meas : ∀ b : ℕ, MeasurableSet (A b))
    (hA_full : ∀ b : ℕ, 2 ≤ b → P (A b) = 1)
    (hA_normal : ∀ b : ℕ, 2 ≤ b → ∀ ω ∈ A b, normalInBase b (Z ω)) :
    ∃ E : Set Ω,
      MeasurableSet E ∧ P E = 1 ∧
        ∀ ω ∈ E, NormalNumber normalInBase (Z ω) := by
  let E : Set Ω := normalNumberFullSet A
  have hE_meas : MeasurableSet E := by
    dsimp [E, normalNumberFullSet]
    exact MeasurableSet.iInter fun b => by
      by_cases hb : 2 ≤ b
      · simpa [hb] using hA_meas b
      · simp [hb]
  have hE_ae : ∀ᵐ ω ∂P, ω ∈ E := by
    have h_each :
        ∀ b : ℕ, ∀ᵐ ω ∂P, ω ∈ (if 2 ≤ b then A b else Set.univ) := by
      intro b
      by_cases hb : 2 ≤ b
      · simpa [hb] using
          (MeasureTheory.mem_ae_iff_prob_eq_one (μ := P) (hA_meas b)).2
            (hA_full b hb)
      · simp [hb]
    filter_upwards [ae_all_iff.2 h_each] with ω hω
    change ω ∈ ⋂ b : ℕ, (if 2 ≤ b then A b else Set.univ)
    exact Set.mem_iInter.2 hω
  have hE_full : P E = 1 :=
    (MeasureTheory.mem_ae_iff_prob_eq_one (μ := P) hE_meas).1 hE_ae
  refine ⟨E, hE_meas, hE_full, ?_⟩
  intro ω hω
  intro b hb
  have hmem_base : ω ∈ (if 2 ≤ b then A b else Set.univ) := by
    change ω ∈ ⋂ b : ℕ, (if 2 ≤ b then A b else Set.univ) at hω
    exact Set.mem_iInter.mp hω b
  have hmem : ω ∈ A b := by
    simpa [hb] using hmem_base
  exact hA_normal b hb ω hmem
