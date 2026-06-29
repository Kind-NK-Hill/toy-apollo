import Mathlib

/-
TASK ID: ex_2_2_1
TYPE: Example_Proof
SOURCE PLAN: 41_chap2_algebra_of_events
TASK CONTENT:
\textbf{Example 2.2.1 (Information Embedded in the Partition of Sample Space)} \\
Alice generates two random bits of information. Whether the bits are uniformly distributed or statistically independent is not relevant in this example. We are interested in the possible events that Alice can observe. Naturally, Alice can take the sample space
\[
\Omega=\{00,01,10,11\}
\]
as the set of all outcomes. Any subset of $\Omega$ is a valid event that Alice can observe.

Alice has two friends Bob and Cindy. Bob wants to determine the number of ones that appear among the two random bits, and Cindy wants to know whether the two bits are the same. Upon observing the generated bits, Alice will inform Bob of an integer between 0 and 2. Bob will know that one of the following three events has occurred:
\[
\{00\}, \{01,10\}, \{11\}.
\]

Alice will inform Cindy that one of the events
\[
\{00,11\}, \{10,01\}
\]
occurred. In fact, Alice does not need to inform Cindy herself. Alice may ask Bob to tell Cindy whether the two bits are the same, as Bob has enough information to do so. Mathematically speaking, this is because Cindy's partition of the sample space is coarser than Bob's partition, meaning that Bob has more detailed information about the possible outcomes of the random bits.

This example illustrates that in some cases, we may only be interested in certain subsets of the sample space. In order to work with these subsets in a rigorous mathematical way, we need to define a collection of events that is closed under the usual set operations. This leads us to the notion of an algebra of events.
-/

-- WRITE FINAL LEAN CODE BELOW

import Mathlib

open Set

abbrev TwoBits := Bool × Bool

/-- The outcome `00`. -/
def bit00 : TwoBits := (false, false)

/-- The outcome `01`. -/
def bit01 : TwoBits := (false, true)

/-- The outcome `10`. -/
def bit10 : TwoBits := (true, false)

/-- The outcome `11`. -/
def bit11 : TwoBits := (true, true)

/-- Alice's sample space of all two-bit outcomes. -/
def twoBitSampleSpace : Set TwoBits := Set.univ

def onesCount (ω : TwoBits) : ℕ :=
  cond ω.1 1 0 + cond ω.2 1 0

/-- Bob's cell for zero ones: `{00}`. -/
def bobZeroOnes : Set TwoBits := {bit00}

/-- Bob's cell for one one: `{01, 10}`. -/
def bobOneOne : Set TwoBits := {bit01, bit10}

/-- Bob's cell for two ones: `{11}`. -/
def bobTwoOnes : Set TwoBits := {bit11}

def bobPartition : Set (Set TwoBits) :=
  {bobZeroOnes, bobOneOne, bobTwoOnes}

/-- Cindy's cell for equal bits: `{00, 11}`. -/
def cindySameBits : Set TwoBits := {bit00, bit11}

/-- Cindy's cell for different bits: `{10, 01}`. -/
def cindyDifferentBits : Set TwoBits := {bit10, bit01}

def cindyPartition : Set (Set TwoBits) :=
  {cindySameBits, cindyDifferentBits}

/-- The explicit zero-one Bob cell agrees with the ones-count description. -/
theorem bobZeroOnes_eq_count_zero : bobZeroOnes = {ω | onesCount ω = 0} := by
  ext ω
  cases ω with
  | mk b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [bobZeroOnes, bit00, onesCount]

/-- The explicit one-one Bob cell agrees with the ones-count description. -/
theorem bobOneOne_eq_count_one : bobOneOne = {ω | onesCount ω = 1} := by
  ext ω
  cases ω with
  | mk b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [bobOneOne, bit01, bit10, onesCount]

/-- The explicit two-ones Bob cell agrees with the ones-count description. -/
theorem bobTwoOnes_eq_count_two : bobTwoOnes = {ω | onesCount ω = 2} := by
  ext ω
  cases ω with
  | mk b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [bobTwoOnes, bit11, onesCount]

/-- Cindy's equal-bit cell agrees with the equality-of-bits description. -/
theorem cindySameBits_eq_same : cindySameBits = {ω | ω.1 = ω.2} := by
  ext ω
  cases ω with
  | mk b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [cindySameBits, bit00, bit11]

/-- Cindy's different-bit cell agrees with the inequality-of-bits description. -/
theorem cindyDifferentBits_eq_different : cindyDifferentBits = {ω | ω.1 ≠ ω.2} := by
  ext ω
  cases ω with
  | mk b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [cindyDifferentBits, bit01, bit10]

/-- Every Bob cell is contained in some Cindy cell, so Bob's information is finer. -/
def BobRefinesCindy : Prop :=
  ∀ ⦃B : Set TwoBits⦄, B ∈ bobPartition → ∃ C ∈ cindyPartition, B ⊆ C

/-- Exported proposition for Example 2.2.1. -/
def ex_2_2_1 : Prop := BobRefinesCindy

/-- Bob's three-cell partition refines Cindy's two-cell partition. -/
theorem bob_refines_cindy : BobRefinesCindy := by
  intro B hB
  simp [bobPartition] at hB
  rcases hB with hB | hB | hB
  · refine ⟨cindySameBits, by simp [cindyPartition], ?_⟩
    rw [hB]
    intro ω hω
    simp [bobZeroOnes, cindySameBits, bit00, bit11] at hω ⊢
    exact Or.inl hω
  · refine ⟨cindyDifferentBits, by simp [cindyPartition], ?_⟩
    rw [hB]
    intro ω hω
    simp [bobOneOne, cindyDifferentBits, bit01, bit10] at hω ⊢
    rcases hω with hω | hω
    · exact Or.inr hω
    · exact Or.inl hω
  · refine ⟨cindySameBits, by simp [cindyPartition], ?_⟩
    rw [hB]
    intro ω hω
    simp [bobTwoOnes, cindySameBits, bit00, bit11] at hω ⊢
    exact Or.inr hω

/-- The exported example proposition holds. -/
theorem ex_2_2_1_holds : ex_2_2_1 :=
  bob_refines_cindy

