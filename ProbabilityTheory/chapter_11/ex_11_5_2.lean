/-
TASK ID: ex_11_5_2
TYPE: Example_Proof
SOURCE PLAN: chapter11-strong-law-large-numbers
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import Mathlib
import ProbabilityTheory.chapter_11.thm_11_8




-- WRITE FINAL LEAN CODE BELOW

open MeasureTheory
open Set



def NormalNumber (normalInBase : ℕ → ℝ → Prop) (x : ℝ) : Prop :=
  ∀ b : ℕ, 2 ≤ b → normalInBase b x

 
def normalNumberFullSet {Ω : Type*} (A : ℕ → Set Ω) : Set Ω :=
  ⋂ b : ℕ, if 2 ≤ b then A b else Set.univ



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
