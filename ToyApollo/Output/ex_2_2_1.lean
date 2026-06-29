/-
TASK ID: ex_2_2_1
TYPE: Example_Proof
SOURCE PLAN: 41_chap2_algebra_of_events
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib

-- WRITE FINAL LEAN CODE BELOW

import Mathlib

open Set

abbrev TwoBits := Bool × Bool

def bit00 : TwoBits := (false, false)

def bit01 : TwoBits := (false, true)

def bit10 : TwoBits := (true, false)

def bit11 : TwoBits := (true, true)

def twoBitSampleSpace : Set TwoBits := Set.univ

def onesCount (ω : TwoBits) : ℕ :=
  cond ω.1 1 0 + cond ω.2 1 0

def bobZeroOnes : Set TwoBits := {bit00}

def bobOneOne : Set TwoBits := {bit01, bit10}

def bobTwoOnes : Set TwoBits := {bit11}

def bobPartition : Set (Set TwoBits) :=
  {bobZeroOnes, bobOneOne, bobTwoOnes}

def cindySameBits : Set TwoBits := {bit00, bit11}

def cindyDifferentBits : Set TwoBits := {bit10, bit01}

def cindyPartition : Set (Set TwoBits) :=
  {cindySameBits, cindyDifferentBits}

theorem bobZeroOnes_eq_count_zero : bobZeroOnes = {ω | onesCount ω = 0} := by
  ext ω
  cases ω with
  | mk b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [bobZeroOnes, bit00, onesCount]

theorem bobOneOne_eq_count_one : bobOneOne = {ω | onesCount ω = 1} := by
  ext ω
  cases ω with
  | mk b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [bobOneOne, bit01, bit10, onesCount]

theorem bobTwoOnes_eq_count_two : bobTwoOnes = {ω | onesCount ω = 2} := by
  ext ω
  cases ω with
  | mk b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [bobTwoOnes, bit11, onesCount]

theorem cindySameBits_eq_same : cindySameBits = {ω | ω.1 = ω.2} := by
  ext ω
  cases ω with
  | mk b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [cindySameBits, bit00, bit11]

theorem cindyDifferentBits_eq_different : cindyDifferentBits = {ω | ω.1 ≠ ω.2} := by
  ext ω
  cases ω with
  | mk b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp [cindyDifferentBits, bit01, bit10]

def BobRefinesCindy : Prop :=
  ∀ ⦃B : Set TwoBits⦄, B ∈ bobPartition → ∃ C ∈ cindyPartition, B ⊆ C

def ex_2_2_1 : Prop := BobRefinesCindy

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

theorem ex_2_2_1_holds : ex_2_2_1 :=
  bob_refines_cindy
