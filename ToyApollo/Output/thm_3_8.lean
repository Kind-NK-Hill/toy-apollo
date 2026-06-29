/-
TASK ID: thm_3_8
SOURCE MATERIAL: omitted from the public source snapshot; see docs/repository_scope.md.
-/

import ToyApollo.Output.def_3_10
import Mathlib.MeasureTheory.Measure.Restrict

open MeasureTheory Set ENNReal

theorem thm_3_8 {Ω : Type*} [m : MeasurableSpace Ω] (F₀ : Set (Set Ω))
  (h_gen : m = MeasurableSpace.generateFrom F₀)
  (h_field_empty : ∅ ∈ F₀)
  (h_field_compl : ∀ s ∈ F₀, sᶜ ∈ F₀)
  (h_field_union : ∀ s ∈ F₀, ∀ t ∈ F₀, s ∪ t ∈ F₀)
  (μ1 μ2 : Measure Ω)
  (h_eq_on_F₀ : ∀ s ∈ F₀, μ1 s = μ2 s)
  (Ω_seq : ℕ → Set Ω)
  (h_disj : Pairwise (fun i j => Disjoint (Ω_seq i) (Ω_seq j)))
  (h_in_F₀ : ∀ i, Ω_seq i ∈ F₀)
  (h_univ : (⋃ i, Ω_seq i) = univ)
  (h_finite : ∀ i, μ1 (Ω_seq i) = μ2 (Ω_seq i) ∧ μ1 (Ω_seq i) < ⊤) :
  μ1 = μ2 := by
  apply Measure.ext_of_generateFrom_of_iUnion F₀ Ω_seq h_gen
  · intro s hs t ht _
    have : s ∩ t = (sᶜ ∪ tᶜ)ᶜ := by ext x; simp
    rw [this]
    exact h_field_compl _ (h_field_union _ (h_field_compl _ hs) _ (h_field_compl _ ht))
  · exact h_univ
  · exact h_in_F₀
  · intro i; exact (h_finite i).2.ne
  · exact h_eq_on_F₀
